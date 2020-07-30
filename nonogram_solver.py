import flask
from flask import Flask, request
from datetime import datetime
import subprocess
import codecs
import os

app = Flask(__name__)


@app.route("/", methods=["GET"])
def index():
    # Content-TypeがJSONでないリクエストは受け付けない。
    if request.headers['Content-Type'] != 'application/json':
        print(request.headers['Content-Type'])
        return flask.jsonify(res='error'), 400

    # ========================================================================
    # JSONに積まれているイラストロジックの行情報と列情報を変数に取得する。
    # ========================================================================
    rows = request.json['Rows']
    cols = request.json['Cols']
    row_len = len(rows)
    col_len = len(cols)
    print('Size : ' + str(row_len) + ' * ' + str(col_len))
    print('------------------------------------')

    # ========================================================================
    # イラストロジックの問題を、Sugar用の問題文（CSP）に書き換える。
    # ========================================================================
    nonogram_csp = ''  # この変数にSugar用の問題文を作り込んでいく。

    for i in range(0, row_len):
        for j in range(0, col_len):
            nonogram_csp += '(int x_' + str(i) + '_' + str(j) + ' 0 1)' + '\n'

    for i in range(0, row_len):
        row_nums = rows[i].split('_')
        for j in range(0, len(row_nums)):
            num = int(row_nums[j])
            nonogram_csp += '(int h_' + str(i) + '_' + str(j) + ' 0 ' + str(col_len - num) + ')' + '\n'

        nonogram_csp += '(predicate (r_' + str(i) + ' j) (or'
        for j in range(0, len(row_nums)):
            num = int(row_nums[j])
            nonogram_csp += ' (and (<= h_' + str(i) + '_' + str(j) + ' j) (< j (+ h_' + str(i) + '_' + str(
                j) + ' ' + str(num) + ')))'
        nonogram_csp += '))' + '\n'
        for j in range(0, col_len):
            nonogram_csp += '(iff (= x_' + str(i) + '_' + str(j) + ' 1) (r_' + str(i) + ' ' + str(j) + '))' + '\n'

    for i in range(0, col_len):
        col_nums = cols[i].split('_')
        for j in range(0, len(col_nums)):
            num = int(col_nums[j])
            nonogram_csp += '(int v_' + str(i) + '_' + str(j) + ' 0 ' + str(row_len - num) + ')' + '\n'

        nonogram_csp += '(predicate (c_' + str(i) + ' j) (or'
        for j in range(0, len(col_nums)):
            num = int(col_nums[j])
            nonogram_csp += ' (and (<= v_' + str(i) + '_' + str(j) + ' j) (< j (+ v_' + str(i) + '_' + str(
                j) + ' ' + str(num) + ')))'
        nonogram_csp += '))' + '\n'
        for j in range(0, row_len):
            nonogram_csp += '(iff (= x_' + str(j) + '_' + str(i) + ' 1) (c_' + str(i) + ' ' + str(j) + '))' + '\n'

    for i in range(0, row_len):
        row_nums = rows[i].split('_')
        for j in range(0, len(row_nums) - 1):
            num = int(row_nums[j])
            nonogram_csp += '(< (+ h_' + str(i) + '_' + str(j) + ' ' + str(num) + ') h_' + str(i) + '_' + str(
                j + 1) + ')' + '\n'

    for i in range(0, col_len):
        col_nums = cols[i].split('_')
        for j in range(0, len(col_nums) - 1):
            num = int(col_nums[j])
            nonogram_csp += '(< (+ v_' + str(i) + '_' + str(j) + ' ' + str(num) + ') v_' + str(i) + '_' + str(
                j + 1) + ')' + '\n'

    # ========================================================================
    # 作ったCSPをファイルに書き出す。
    # ========================================================================
    filename = 'nonogram_' + datetime.now().strftime('%Y.%m.%d.%H.%M.%S') + '.csp'
    print(nonogram_csp, file=codecs.open(filename, 'w', 'utf-8'))

    # ========================================================================
    # 問題をSugarに渡し、解かせる。
    # ========================================================================
    args = ['sugar', './' + filename]
    res = subprocess.check_output(args).decode('utf-8')
    res_rows = res.splitlines()
    res_len = len(res_rows)

    # ========================================================================
    # 解があった場合は後続処理に進む。
    # 解がなかった場合は「Oops! Your question has no answer!」とレスポンスを返して処理を終了する。
    # ========================================================================
    answer_picture = ''  # 解いた結果の絵をこの変数に収める。
    multi_answer_check_formula = ''  # 複数解有無のチェックを行うためにCSP末尾に追加する条件をこの変数に収める。
    has_multi_answer = False  # 複数解があった場合、この変数をTrueに変更する。
    if 's SATISFIABLE' != res_rows[0]:
        os.remove(filename)
        return 'Oops! Your question has no answer!'

    # ========================================================================
    # CSPファイルの末尾に「今さっきの解答と完全一致しないものとする」という条件を加え、
    # 再度Sugarに問題を渡し、解かせる。
    # ========================================================================
    row_num = 0
    col_num = 0
    multi_answer_check_formula += '\n' + '(not (and '
    for i in range(1, res_len):
        res_row_parts = res_rows[i].split('_')
        if res_row_parts[0] == 'a x':
            last_val = res_row_parts[2].split('\t')[1]
            if row_num != int(res_row_parts[1]):
                col_num = 0
                answer_picture += '\n'
                row_num = int(res_row_parts[1])
            if int(last_val) == 0:
                multi_answer_check_formula += '(= x_' + str(row_num) + '_' + str(col_num) + ' 0)'
                answer_picture += '.'
            elif int(last_val) == 1:
                multi_answer_check_formula += '(= x_' + str(row_num) + '_' + str(col_num) + ' 1)'
                answer_picture += '#'
            col_num += 1
    multi_answer_check_formula += '))'

    print(multi_answer_check_formula, file=codecs.open(filename, 'a', 'utf-8'))
    multicheck_res = subprocess.check_output(args).decode('utf-8')
    multicheck_res_rows = multicheck_res.splitlines()
    if 's SATISFIABLE' == multicheck_res_rows[0]:
        has_multi_answer = True

    os.remove(filename)

    # ========================================================================
    # 解があった場合は「Oops! Your question has multi answer!」とレスポンスを返す。
    # 解がなかった場合は、解答の絵を返す。
    # ========================================================================
    if has_multi_answer:
        print(answer_picture)
        return 'Oops! Your question has multi answer!'
    else:
        print(answer_picture)
        print('------------------------------------')
        return answer_picture


if __name__ == '__main__':
    app.run(port=5000, debug=True)
