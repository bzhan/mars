from flask import Flask
from flask import request
import lark
import json

from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.server.get_port_service import get_aadl_port_service, get_simulink_port_service

app = Flask(__name__)


@app.route('/')
def hello_world():
    return "Hello, World!"

def raise_error(err_str):
    return json.dumps({
        'error': err_str
    })

@app.route('/parse_hcsp', methods=['POST'])
def parse_hcsp():
    data = json.loads(request.get_data())
    text = data['text']
    text_lines = text.strip().split('\n')
    hcsp_info = []
    for i, line in enumerate(text_lines):
        try:
            index = line.index('::=')
        except ValueError:
            return raise_error("Line %s must contain '::='.\n  %s" % (str(i+1), line))

        name = line[:index].strip()
        hp_text = line[index+3:].strip()

        try:
            hp = parser.hp_parser.parse(hp_text)
        except (lark.exceptions.UnexpectedToken, lark.exceptions.UnexpectedCharacters) as e:
            indicator_str = " " * (e.column-1) + "^"
            return raise_error("Unable to parse:\n  %s\n  %s" % (hp_text, indicator_str))

        if hp.type == 'parallel':
            if not all(sub_hp.type == 'var' for sub_hp in hp.hps):
                return raise_error("Group definition must be a parallel of variables.\n  %s" % line)

            hcsp_info.append({
                'name': name,
                'parallel': [sub_hp.name for sub_hp in hp.hps]
            })
        else:
            lines, mapping = pprint.pprint_lines(hp, record_pos=True)
            hcsp_info.append({
                'name': name,
                'text': hp_text,
                'lines': lines,
                'mapping': mapping
            })

    return json.dumps({
        'hcsp_info': hcsp_info,
    })

@app.route('/run_hcsp', methods=['POST'])
def run_hcsp():
    data = json.loads(request.get_data())
    infos = data['hcsp_info']
    num_io_events = data['num_io_events']
    num_steps = data['num_steps']

    infos = [simulator.HCSPInfo(info['name'], info['text']) for info in infos if 'parallel' not in info]
    try:
        res = simulator.exec_parallel(infos, num_steps=num_steps, num_io_events=num_io_events)
    except simulator.SimulatorException as e:
        return raise_error(e.error_msg)

    return json.dumps(res)

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
