from flask import Flask
from flask import request
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser

app = Flask(__name__)


def postprocess(new_code, hcsp_state, reason):
    new_code, reason = str(new_code), str(reason)

    new_state = {}

    for key in hcsp_state.keys():
        val = hcsp_state[key]
        new_state[key.value] = val

    return new_code, new_state, reason


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

    new_code, new_state, reason = postprocess(new_cmd, hcsp_input, reason)

    result = {'new_code': new_code, 'new_state': new_state, 'reason': reason}

    result = json.dumps(result)
    return result

@app.route('/step', methods=['POST'])
def step():
    data = json.loads(request.get_data(as_text=True))
    hcsp_code = data['code']
    hcsp_state = data['state']

    hcsp_code = parser.hp_parser.parse(hcsp_code)
    hcsp_code, reason = simulator.exec_step(hcsp_code, hcsp_state)

    result = {'new_code': hcsp_code, 'new_state': hcsp_state, 'reason': str(reason)}

    result = json.dumps(result)
    return result



if __name__ == '__main__':
    app.run(debug=True)
