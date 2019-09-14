from flask import Flask
from flask import request
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.server.get_port_service import get_aadl_port_service, get_simulink_port_service

app = Flask(__name__)


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
    history = []
    time_series = []
    time, events = simulator.exec_parallel(info, num_steps, state_log=history, time_series=time_series)
    if events[-1] != 'deadlock':
        events = [{'time': 0, 'str': 'start'}] + events + [{'time': time, 'str': 'end'}]
    else:
        events = [{'time': 0, 'str': 'start'}] + events

    return json.dumps({
        'history': history,
        'events': events,
        'time_series': time_series,
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
