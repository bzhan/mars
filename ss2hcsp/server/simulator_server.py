

from ss2hcsp.server.sequence_diagram import print_sequence_diagram
from ss2hcsp.server.get_port_service import get_aadl_port_service, get_simulink_port_service
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import pprint
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import simulator
from flask import Flask
from flask import request
import lark
import json
import math
import time
from pstats import Stats
import cProfile
import random

import sys
sys.path.append("..")

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
        name, hp, procs = info.name, info.hp, info.procedures
        if hp.type == 'parallel':
            if not all(sub_hp.type == 'var' for sub_hp in hp.hps):
                return raise_error("Group definition must be a parallel of variables.\n  %s" % line)

            hcsp_info.append({
                'name': name,
                'parallel': [sub_hp.name for sub_hp in hp.hps]
            })
        else:
            procs = dict()
            for proc in info.procedures:
                procs[proc.name] = proc
            sim_infos.append(simulator.SimInfo(
                name, hp, outputs=info.outputs, procedures=procs))
            lines, mapping = pprint.pprint_lines(hp, record_pos=True)
            json_procs = []
            for proc in info.procedures:
                proc_lines, proc_mapping = pprint.pprint_lines(
                    proc.hp, record_pos=True)
                json_procs.append({
                    'name': proc.name,
                    'text': str(proc.hp),
                    'lines': proc_lines,
                    'mapping': proc_mapping
                })
            hcsp_info.append({
                'name': name,
                'text': str(hp),
                'outputs': [output.toJson() for output in info.outputs],
                'lines': lines,
                'mapping': mapping,
                'procedures': json_procs
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
    num_steps = data['num_steps']
    profile = False

    def convert_procs(procs):
        return {proc['name']: hcsp.Procedure(proc['name'], proc['text'])
                for proc in procs}

    infos = [simulator.SimInfo(info['name'], info['text'],
                               outputs=[hcsp.outputFromJson(
                                   output) for output in info['outputs']],
                               procedures=convert_procs(info['procedures']))
             for info in infos if 'parallel' not in info]

    num_show = data['num_show']
    show_interval = 40000 if num_show > 40000 else None
    if 'start_event' in data:
        start_event = data['start_event']
    else:
        start_event = None

    if profile:
        pr = cProfile.Profile()
        pr.enable()

    try:
        random.seed(0)
        clock = time.perf_counter()
        res = simulator.exec_parallel(
            infos, num_steps=num_steps, num_show=num_show, show_interval=show_interval,
            start_event=start_event)
        print("Time:", time.perf_counter() - clock)

        # # export the time series data of Plant to files
        # directory = "/Users/BEAR/Projects/mars/Examples/AADL/CCS/TCS/data/"
        # s_file = open(directory + 'HCSP_s_3bus_7ms_p1s_noise_con8', 'w')
        # v_file = open(directory + 'HCSP_v_3bus_7ms_p1s_noise_con8', 'w')
        # for time_states in res['time_series']['vehicle_imp']:
        #     if 's' in time_states['state']:
        #         s_file.write(str(time_states['time']) + ',')
        #         s_file.write(str(time_states['state']['s']) + '\n')
        #     if 'v' in time_states['state']:
        #         v_file.write(str(time_states['time']) + ',')
        #         v_file.write(str(time_states['state']['v']) + '\n')
        # s_file.close()
        # v_file.close()
        #
        # obs_file = open(directory + 'HCSP_obs_3bus_7ms_p1s_noise_con8', 'w')
        # for time_states in res['time_series']['emerg_imp']:
        #     if 'obs_pos' in time_states['state']:
        #         obs_file.write(str(time_states['time']) + ',')
        #         obs_file.write(str(time_states['state']['obs_pos']) + '\n')
        # obs_file.close()
        #
        # print("DONE!")

    except simulator.SimulatorException as e:
        return raise_error(e.error_msg)

    # Process time series, so that each process has at most 10000 events
    for key in res['time_series']:
        l = len(res['time_series'][key])
        if l > 10000:
            new_series = []
            for i in range(10000):
                idx = math.floor(i * (l / 10000.0))
                new_series.append(res['time_series'][key][idx])
            res['time_series'][key] = new_series

    if len(res['trace']) < 2000:
        with open('event_output.json', 'w', encoding='utf-8') as f:
            json.dump(res['trace'], f, indent=4, ensure_ascii=False)

    if len(res['trace']) > 0:
        print_sequence_diagram(res['trace'])

    with open('simulator_events.txt', 'w', encoding='utf-8') as f:
        for i, event in enumerate(res['events']):
            f.write("%s: %s\n" % (i, event))

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

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
    app.run()
