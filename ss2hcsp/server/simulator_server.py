from flask import Flask
from flask import request
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser

app = Flask(__name__)


@app.route('/')
def hello_world():
    return "Hello, World!"


@app.route('/process', methods=['POST'])
def process():
    data = json.loads(request.get_data(as_text=True))
    hcsp_code = data['code']
    hcsp_input = data['input']

    cmd = parser.hp_parser.parse(hcsp_code)

    new_cmd, reason = simulator.exec_process(cmd, hcsp_input)

    new_state = {}

    for key in hcsp_input.keys():
        val = hcsp_input[key]
        new_state[key.value] = val

    new_cmd, reason = str(new_cmd), str(reason)

    result = {'new_code': new_cmd, 'new_state': new_state, 'reason': reason}

    result = json.dumps(result)
    return result


if __name__ == '__main__':
    app.run(debug=True)
