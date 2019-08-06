from flask import Flask
from flask import request
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser
from ss2hcsp.server.simulator_service import process_multi

app = Flask(__name__)


def postprocess(new_code, hcsp_state, reason):
    new_code = str(new_code)
    new_reason = {reason[0]: reason[1]}

    new_state = {}

    for key in hcsp_state.keys():
        val = hcsp_state[key]
        if type(key) != str:
            new_state[key.value] = val
        else:
            new_state[key] = val

    return new_code, new_state, new_reason


@app.route('/')
def hello_world():
    return "Hello, World!"


@app.route('/process', methods=['POST'])
def process():
    data = json.loads(request.get_data(as_text=True))

    print(data)
    hcsp_code = data['code']
    hcsp_input = data['input']
    hcsp_reason = data['reason'] if 'reason' in data.keys() else None

    cmd = parser.hp_parser.parse(hcsp_code)

    if hcsp_reason is None:
        new_cmd, new_reason = simulator.exec_process(cmd, hcsp_input)
    elif 'delay' in hcsp_reason:
        delay_time = hcsp_reason['delay']
        new_cmd = simulator.exec_delay(cmd, hcsp_input, delay_time)
        new_reason = ("process_delay", 3)
    else:
        new_cmd, new_reason = simulator.exec_process(cmd, hcsp_input)
    new_code, new_state, new_reason = postprocess(new_cmd, hcsp_input, new_reason)

    result = {'new_code': new_code, 'new_state': new_state, 'reason': new_reason}

    result = json.dumps(result)
    return result


@app.route('/process_multi', method=['POST'])
def process_multi():
    hcsp_programs = json.loads(request.get_data(as_text=True))
    try:
        result = process_multi(hcsp_programs)
    except:
        return "Service Error"
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


@app.route('/step_multi', methods=['POST'])
def step_multi():
    data = json.loads(request.get_data(as_text=True))
    hcsp_programs = data['programs']

    pass


if __name__ == '__main__':
    app.run(debug=True)
