from flask import Flask
from flask import request
import lark
import json
import math
import time

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

    try:
        if text.startswith('%type: module'):
            infos = parser.parse_module_file(text)
        else:
            infos = parser.parse_file(text)
    except parser.ParseFileException as e:
        return raise_error(e.error_msg)

    sim_infos = []
    hcsp_info = []
    for info in infos:
        name, hp = info.name, info.hp
        if hp.type == 'parallel':
            if not all(sub_hp.type == 'var' for sub_hp in hp.hps):
                return raise_error("Group definition must be a parallel of variables.\n  %s" % line)

            hcsp_info.append({
                'name': name,
                'parallel': [sub_hp.name for sub_hp in hp.hps]
            })
        else:
            sim_infos.append(simulator.SimInfo(name, hp, outputs=info.outputs))
            lines, mapping = pprint.pprint_lines(hp, record_pos=True)
            hcsp_info.append({
                'name': name,
                'text': str(hp),
                'outputs': info.outputs,
                'lines': lines,
                'mapping': mapping
            })

    warnings = simulator.check_comms(sim_infos)

    return json.dumps({
        'hcsp_info': hcsp_info,
        'warnings': warnings
    })

@app.route('/run_hcsp', methods=['POST'])
def run_hcsp():
    data = json.loads(request.get_data())
    infos = data['hcsp_info']
    num_io_events = data['num_io_events']
    num_steps = data['num_steps']

    infos = [simulator.SimInfo(info['name'], info['text'], outputs=info['outputs'])
             for info in infos if 'parallel' not in info]

    num_show = data['num_show']
    show_starting = data['show_starting']
    try:
        clock = time.perf_counter()
        res = simulator.exec_parallel(
            infos, num_steps=num_steps, num_io_events=num_io_events, num_show=num_show)
        print("Time:", time.perf_counter() - clock)
    except simulator.SimulatorException as e:
        return raise_error(e.error_msg)

    # Process time series, so that each process has at most 1000 events
    for key in res['time_series']:
        l = len(res['time_series'][key])
        if l > 1000:
            new_series = []
            for i in range(1000):
                idx = math.floor(i * (l / 1000.0))
                new_series.append(res['time_series'][key][idx])
            res['time_series'][key] = new_series

    # When limiting to a range, update info so it does not refer to value
    # outside the range
    # for i in range(show_starting, min(len(res['trace']), show_starting + num_show)):
    #     for name, info in res['trace'][i]['infos'].items():
    #         if isinstance(info, int):
    #             if info < show_starting:
    #                 res['trace'][i]['infos'][name] = res['trace'][info]['infos'][name]
    #             else:
    #                 res['trace'][i]['infos'][name] = info - show_starting

    # res['trace'] = res['trace'][show_starting : show_starting+num_show]

    for key in res.keys():
        print(key, len(json.dumps(res[key])))

    for key in res['time_series']:
        print(key, len(res['time_series'][key]))

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
