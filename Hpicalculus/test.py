
#test for hpicalculus parser
from Hpicalculus import parser
from Hpicalculus import simulator
import random
import time
from Hpicalculus import Hpical
file1 = open("Hpicalculus\case1.txt", "r",encoding='utf-8')
text= file1.read()
file1.close()
infos = parser.parse_file(text)

#test for hcsp parser
# from ss2hcsp.hcsp import parser as pa
# file2 = open("Examples\HCSP\dds_best_effort_continuous.txt", "r")
# text = file2.read()
# file2.close()
# info = pa.parse_file(text)
sim_infos = []
hcsp_info = []
for info in infos:
    name, hp, procs = info.name, info.hp, info.procedures
    if hp.type == 'parallel':
        assert all(sub_hp.type == 'var' for sub_hp in hp.hps)
        hcsp_info.append({
            'name': name,
            'parallel': [sub_hp.name for sub_hp in hp.hps]
        })
    else:
        sim_infos.append(simulator.SimInfo(
            name, hp, outputs=info.outputs, procedures=info.procedures))
       # lines, mapping = pprint.pprint_lines(hp, record_pos=True)
        json_procs = []
        for proc in info.procedures:
            #proc_lines, proc_mapping = pprint.pprint_lines(
            #    proc.hp, record_pos=True)
            json_procs.append({
                'name': proc.name,
                'text': str(proc.hp),
                # 'lines': proc_lines,
                # 'mapping': proc_mapping
            })
        hcsp_info.append({
            'name': name,
            'text': str(hp),
            'outputs': info.outputs,
            # 'lines': lines,
            # 'mapping': mapping,
            'procedures': json_procs
        })

num_steps =200
num_show = 200
start_event = None
show_interval = None


def convert_procs(procs):
        return {proc['name']: Hpical.Procedure(proc['name'], proc['text'])
                for proc in procs}
infos = [simulator.SimInfo(info['name'], info['text'], outputs=info['outputs'],
                               procedures=convert_procs(info['procedures']))
             for info in hcsp_info if 'parallel' not in info]
try:
    random.seed(0)
    clock = time.perf_counter()
    res = simulator.exec_parallel(
        infos, num_steps=num_steps, num_show=num_show, show_interval=show_interval,
        start_event=start_event)
    print("Time:", time.perf_counterprocedu() - clock)

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
    print(e.error_msg)
