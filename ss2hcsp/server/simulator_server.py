from flask import Flask
from flask import request
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.server.simulator_service import process_multi as process_multi_service
from ss2hcsp.server.simulator_service import step_multi as step_multi_service
from ss2hcsp.server.get_port_service import get_aadl_port_service, get_simulink_port_service

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

@app.route('/parse_hcsp', methods=['POST'])
def parse_hcsp():
    data = json.loads(request.get_data())
    hcspCode = data['hcspCode']
    print_info = [pprint.pprint_lines(parser.hp_parser.parse(hp), record_pos=True) for hp in hcspCode]

    return json.dumps({
        'print_info': print_info,
    })

@app.route('/run_hcsp', methods=['POST'])
def run_hcsp():
    data = json.loads(request.get_data())
    hcspCode = data['hcspCode']
    num_steps = data['num_steps']

    info = [simulator.HCSPInfo(hp) for hp in hcspCode]
    history, events = simulator.exec_parallel(info, num_steps, log_state=True)
    if events[-1] != 'deadlock':
        events = ['start'] + events + ['end']
    else:
        events = ['start'] + events

    return json.dumps({
        'history': history,
        'events': events,
    })

@app.route('/run_hcsp_steps', methods=['POST'])
def run_hcsp_steps():
    data = json.loads(request.get_data())
    infos = data['infos']
    infos = [simulator.HCSPInfo(info['hp'], pos=info['pos'], state=info['state']) for info in infos]
    history = simulator.exec_parallel_steps(infos, start_event=data['start_event'])

    return json.dumps({
        'history': history,
    })

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


@app.route('/process_multi', methods=['POST'])
def process_multi():
    hcsp_programs = json.loads(request.get_data(as_text=True))

    result_hcsp_programs = process_multi_service(hcsp_programs)

    # convert to json serializable format
    for program_id in result_hcsp_programs:
        result_hcsp_programs[program_id]["reason"] = {result_hcsp_programs[program_id]["reason"][0]:
                                                          result_hcsp_programs[program_id]["reason"][1]}
        result_hcsp_programs[program_id]["code"] = str(result_hcsp_programs[program_id]["code"])

    return json.dumps(result_hcsp_programs)


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
    hcsp_programs = json.loads(request.get_data(as_text=True))

    result_hcsp_programs = step_multi_service(hcsp_programs)

    # convert to json serializable format
    for program_id in result_hcsp_programs:
        result_hcsp_programs[program_id]["reason"] = {result_hcsp_programs[program_id]["reason"][0]:
                                                          result_hcsp_programs[program_id]["reason"][1]}
        result_hcsp_programs[program_id]["code"] = str(result_hcsp_programs[program_id]["code"])

    return json.dumps(result_hcsp_programs)

@app.route('/get_simulink_port', methods=['POST'])
def get_simulink_port():
    simulink_code = request.get_data(as_text=True)
    ports = get_simulink_port_service(simulink_code)
    return json.dumps(ports)


@app.route('/get_AADL_port', methods=['POST'])
def get_AADL_port():
    aadl_code = request.get_data(as_text=True)
    ports = get_aadl_port_service(aadl_code)
    return json.dumps(ports)




if __name__ == '__main__':
    app.run(debug=True)
