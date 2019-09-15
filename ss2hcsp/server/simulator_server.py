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
    text = data['text']
    text_lines = text.strip().split('\n')
    hcsp_info = []
    for line in text_lines:
        index = line.index('::=')
        name = line[:index].strip()
        hp_text = line[index+3:].strip()
        hp = parser.hp_parser.parse(hp_text)
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
    num_steps = data['num_steps']

    infos = [simulator.HCSPInfo(info['name'], info['text']) for info in infos]
    res = simulator.exec_parallel(infos, num_steps)

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
