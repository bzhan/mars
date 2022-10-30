# New version of translator from JSON to HCSP

import os

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sl.get_hcsp import translate_discrete
from aadl2hcsp.get_modules import get_continuous_module, get_databuffer_module, get_bus_module
from ss2hcsp.sf import sf_convert


def time_str_to_num(time_str):
    if time_str[-2:] == 'ms':
        return int(time_str[:-2]) / 1000.0
    else:
        raise NotImplementedError


thread_template = """
module EXE(sid, name, max_c, DL, priority):
begin
@INIT;
state := "wait"; prior := priority;
{
    if (state == "wait"){
        @INPUT;
        t := 0; entered := 0; state := "ready";
    }else if (state == "ready"){
        reqProcessor[sid][name]!prior;
        {t_dot = 1 & t < DL} |> [] (run[sid][name]? --> state := "running";)
        if(t == DL && state == "ready") {
            exit[sid][name]! --> state := "wait";
            $
            run[sid][name]? --> state := "running";
        }
    }else{
        if(entered == 0) {
            c := 0;
            @DISCRETE_COMPUTATION;
            entered := 1;
        }
        if(entered == 1) {
            {t_dot = 1, c_dot = 1 & c < max_c && t < DL} |> []
            (preempt[sid][name]? --> state := "ready";)
            if(state == "running") {
                if (c == max_c){
                    @OUTPUT;
                    {
                    preempt[sid][name]? --> state := "wait"; 
                    $ 
                    free[sid][name]! --> state := "wait";
                    }
                }else{
                    preempt[sid][name]? --> state := "wait"; 
                    $ 
                    free[sid][name]! --> state := "wait";
                }
            }
        }
    }
}*
end
endmodule
"""

thread_with_bus_template = """
module EXE(sid, name, max_c, DL, priority, bus):
begin
@INIT;
state := "wait"; prior := priority;
{
    if (state == "wait"){
        @INPUT;
        t := 0; entered := 0; state := "ready";
    }else if (state == "ready"){
        reqProcessor[sid][name]!prior;
        {t_dot = 1 & t < DL} |> [] (run[sid][name]? --> state := "running";)
        if(t == DL && state == "ready") {
            exit[sid][name]! --> state := "wait";
            $
            run[sid][name]? --> state := "running";
        }
    }else if (state == "running"){
        if(entered == 0) {
            c := 0;
            @DISCRETE_COMPUTATION;
            entered := 1;
        }
        if(entered == 1) {
            {t_dot = 1, c_dot = 1 & c < max_c && t < DL} |> []
            (preempt[sid][name]? --> state := "ready";)
            if(state == "running") {
                    if (c == max_c){ 
                        reqBus[name]! --> {@OUTPUT; {preempt[sid][name]? --> state := "wait"; $ free[sid][name]! --> state := "wait";}}
                        $
                        block[name]? --> {preempt[sid][name]? --> state := "await"; $ free[sid][name]! --> state := "await";}
                    }else{
                        preempt[sid][name]? --> state := "wait"; 
                        $
                        free[sid][name]! --> state := "wait";
                    }
            }
        }
    }else{
        {t_dot = 1 & t < 0.005} |> [] (unblock["emerg"]? --> state := "ready";)
        if(t == 0.005) {state := "wait";}
    }
}*
end
endmodule
"""


def translate_thread(name, info, bus=None):
    """Translate to HCSP module for threads."""
    max_c = time_str_to_num(info['compute_execution_time'])
    DL = time_str_to_num(info['deadline'])
    priority = info['priority']
    args = [expr.AConst(0),
            expr.AConst(name),
            expr.AConst(max_c),
            expr.AConst(DL),
            expr.AConst(priority)]
    if bus:
        mod = parser.module_parser.parse(thread_with_bus_template)
        args.append(expr.AConst(bus))
    else:
        mod = parser.module_parser.parse(thread_template)
    mod_inst = module.HCSPModuleInst("EXE" + name, "EXE", args)
    hp_info = mod_inst.generateInst(mod)

    # Input procedure
    def get_input(port, var_name):
        return hcsp.InputChannel(hcsp.Channel("inputs", (expr.AConst(name), expr.AConst(port))), var_name)

    def get_event_input(event_port, event_val):
        return (hcsp.InputChannel(hcsp.Channel("dis", (expr.AConst(name), expr.AConst(event_port))), "event"),
                hcsp.Skip())

    if info['dispatch_protocol'] == 'periodic':
        input_dis = hcsp.InputChannel(
            hcsp.Channel("dis", (expr.AConst(name),)))
        inputs = [get_input(port, port_info['var'])
                  for port, port_info in info['input'].items()]
        input_hp = hcsp.Sequence(*([input_dis] + inputs))
    elif info['dispatch_protocol'] == 'aperiodic':
        io_comms = [get_event_input(event_port, event_val)
                    for event_port, event_val in info['event_input'].items()]
        input_hp = hcsp.SelectComm(
            *io_comms) if len(io_comms) >= 2 else io_comms[0][0]
    else:
        raise NotImplementedError

    # Output procedure
    def get_output(port, var_name):
        return hcsp.OutputChannel(hcsp.Channel("outputs", (expr.AConst(name), expr.AConst(port))),
                                  hcsp.AVar(var_name))
    outputs = [get_output(port, var_name)
               for port, var_name in info['output'].items()]

    # Discrete Computation: convert from Simulink diagram to HCSP
    def get_discrete_computation(location):
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        _init_hps, _procedures, _output_hps, _update_hps, _ =\
            translate_discrete(list(diagram.blocks_dict.values()), None)
        if len(_init_hps) >= 2:
            _init_hps = hcsp.Sequence(*_init_hps)
        elif len(_init_hps) == 1:
            _init_hps = _init_hps[0]
        else:
            _init_hps = ""
        _procedures = [hcsp.Procedure(name=_name, hp=_hcsp)
                       for _name, _hcsp in _procedures]
        _hps = [_hcsp for _hcsp in _output_hps + _update_hps]
        if len(_hps) >= 2:
            _hps = hcsp.Sequence(*_hps)
        elif len(_hps) == 1:
            _hps = _hps[0]
        else:
            _hps = hcsp.Skip()
        return _init_hps, _procedures, _hps

    # Convert from Stateflow diagram to HCSP
    def get_stateflow_computation(location):
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.add_line_name()
        charts = [block for block in diagram.blocks_dict.values() if block.type == "stateflow"]
        assert len(charts) == 1
        converter = sf_convert.SFConvert(charts[0], chart_parameters=diagram.chart_parameters[charts[0].name],
                                         translate_io=False)
        _init_hp = hcsp.Var(converter.init_name(charts[0].name))
        _dis_comp = hcsp.Var(converter.exec_name(charts[0].name))
        _procedures = converter.get_procs()
        procs = []
        for _name, _hp in _procedures.items():
            procs.append(hcsp.Procedure(_name, _hp))

        return _init_hp, procs, _dis_comp

    initializations = list()
    if 'initialization' in info.keys():
        initializations.append(parser.hp_parser.parse(info['initialization']))
    if info['impl'] == "Simulink":
        init_hp, procedures, dis_comp = \
            get_discrete_computation(location=info['discrete_computation'])
        if init_hp:
            initializations.append(init_hp)
    elif info['impl'] == "Stateflow":
        init_hp, procedures, dis_comp = \
            get_stateflow_computation(location=info['discrete_computation'])
        initializations.append(init_hp)
    else:
        raise NotImplementedError

    inst = {
        "INIT": hcsp.Sequence(*initializations) if initializations else hcsp.Skip(),
        "INPUT": input_hp,
        "DISCRETE_COMPUTATION": hcsp.Sequence(parser.hp_parser.parse("%s_impEL := push(%s_impEL, event);"%(name,name),),
                                              dis_comp,
                                              parser.hp_parser.parse("%s_impEL := pop(%s_impEL);"%(name,name)))
        if "event_input" in info else dis_comp,
        "OUTPUT": hcsp.Sequence(*outputs)
    }
    hp = hcsp.HCSP_subst(hp_info.hp, inst)
    return module.HCSPModule(name="EXE_" + name, code=hp, procedures=procedures,
                             outputs=info["display"])


def translate_device(name, info):
    """Translate to HCSP module for devices."""
    if info['impl'] == 'HCSP':
        hp = parser.hp_parser.parse(info['discrete_computation'])
        # new_mod = module.HCSPModule("DEVICE_" + name, [], [], hp)
        new_mod = module.HCSPModule(
            name="DEVICE_" + name, code=hp, outputs=info['display'])
        return new_mod

    elif info['impl'] == 'Channel':
        # Input procedure
        def get_input(port, var_name):
            return hcsp.InputChannel(hcsp.Channel("inputs", (expr.AConst(name), expr.AConst(port))), var_name)
        inputs = [get_input(port, port_info['var'])
                  for port, port_info in info['input'].items()]

        # Output procedure
        def get_output(port, var_name):
            return hcsp.OutputChannel(hcsp.Channel("outputs", (expr.AConst(name), expr.AConst(port))), hcsp.AVar(var_name))
        outputs = [get_output(port, var_name)
                   for port, var_name in info['output'].items()]

        # Wait
        delay = time_str_to_num(info['period'])
        wait_hp = hcsp.Wait(expr.AConst(delay))

        hp = hcsp.Loop(hcsp.Sequence(*(inputs + outputs + [wait_hp])))
        return module.HCSPModule(name="DEVICE_" + name, code=hp, outputs=info['display'])

    else:
        raise NotImplementedError


def translate_abstract(name, info):
    """Translate to HCSP module for abstract components (plants)"""
    if info['impl'] == 'Simulink':
        diagram = SL_Diagram(location=info['discrete_computation'])
        _ = diagram.parse_xml()
        diagram.add_line_name()

        # get ports {port_name: port_type}
        ports = dict()
        inputvalues= dict()
        for port_name, var_dict in info["input"].items():
            assert port_name not in ports
            ports[port_name] = (var_dict['var'], "in data")
            inputvalues[port_name] = (var_dict['var'], var_dict['val'])
        for port_name, var_name in info["output"].items():
            assert port_name not in ports
            ports[port_name] = (var_name, "out data")
        return get_continuous_module(name="PHY_"+name,
                                     ports=ports,
                                     inputvalues= inputvalues,
                                     continuous_diagram=list(diagram.blocks_dict.values()),
                                     outputs=info['display'])

    else:
        raise NotImplementedError


def translate_bus(name, info, json_info):
    latency = time_str_to_num(info['latency'])
    thread_ports = dict()
    device_ports = dict()
    for _info in json_info.values():
        if _info['category'] == "connection" and ('bus' in _info.keys()):
            if _info['category'] == "connection" and _info['bus'] == name:
                source = _info['source']
                source_port = _info['source_port']
                _type = "out " + _info['type']
                if json_info[source]['category'] == "thread":
                    if source not in thread_ports:
                        thread_ports[source] = {source_port: _type}
                    else:
                        assert source_port not in thread_ports[source]
                        thread_ports[source][source_port] = _type
                elif json_info[source]['category'] == "device":
                    if source not in device_ports:
                        device_ports[source] = {source_port: _type}
                    else:
                        assert source_port not in device_ports[source]
                        device_ports[source][source_port] = _type
    return get_bus_module(name, thread_ports, device_ports, latency)


def translate_system(json_info):
    """Construct description of the system"""
    # Construct the components
    component_mod_insts = [module.HCSPModuleInst(
        "scheduler", "SchedulerHPF", [expr.AConst(0)])]
    for name, info in json_info.items():
        if info['category'] == 'thread':
            if info['dispatch_protocol'] == 'periodic':
                component_mod_insts.append(module.HCSPModuleInst("ACT_" + name, "ACT_periodic", [
                    expr.AConst(name), expr.AConst(
                        time_str_to_num(info['period']))
                ]))
            component_mod_insts.append(
                module.HCSPModuleInst(name, "EXE_" + name, []))

        elif info['category'] == 'device':
            component_mod_insts.append(
                module.HCSPModuleInst(name, "DEVICE_" + name, []))

        elif info['category'] == 'abstract':
            component_mod_insts.append(
                module.HCSPModuleInst(name, "PHY_" + name, []))

        elif info['category'] == 'connection':
            source = info['source']
            source_port = info['source_port']
            targets = info['target']
            target_ports = info['target_port']
            assert len(targets) == len(target_ports)

            if 'bus' in info.keys():
                source = info['bus']
            args = [expr.AConst(source), expr.AConst(source_port)]

            for target, target_port in zip(targets, target_ports):
                args.append(expr.AConst(target))
                args.append(expr.AConst(target_port))
            if info['type'] == "data":
                args.append(expr.AConst(info['init_value']))
                component_mod_insts.append(module.HCSPModuleInst(
                    name, "DataBuffer"+str(len(targets)), args))
                # if info['bus']:
                #     component_mod_insts.append(module.HCSPModuleInst("busDataBuffer_"+name,
                #                                                      "DataBuffer"+str(len(targets)),
                #                                                      [expr.AConst(info['source']),
                #                                                       expr.AConst(source_port),
                #                                                       expr.AConst(source),
                #                                                       expr.AConst(source_port),
                #                                                       expr.AConst(0)]))
            elif info['type'] == "event":
                assert len(targets) == 1
                component_mod_insts.append(
                    module.HCSPModuleInst(name, "EventBuffer", args))
                if info['bus']:
                    component_mod_insts.append(module.HCSPModuleInst("busEventBuffer_"+name, "BusEventBuffer",
                                                                     [expr.AConst(info['source']),
                                                                      expr.AConst(
                                                                          source_port),
                                                                      expr.AConst(
                                                                          source),
                                                                      expr.AConst(source_port)]))
            else:
                raise NotImplementedError
        elif info['category'] == 'bus':
            component_mod_insts.append(
                module.HCSPModuleInst(name, "Bus_"+name, []))
        elif info['category'] == 'processor':
            continue
        else:
            raise NotImplementedError

    return component_mod_insts


def translate_aadl_from_json(jsoninfo, output):
    mods = list()
    dataBuffers = dict()  # {recv_num: databuffer}
    buses = list()
    for name, content in jsoninfo.items():
        if content['category'] == 'thread':
            mod = translate_thread(name, content)
            for _content in jsoninfo.values():
                if _content['category'] == "connection" and _content['source'] == name and ('bus' in _content.keys()):
                    mod = translate_thread(name, content, _content['bus'])
                    break
            mods.append(mod)
        elif content['category'] == 'device':
            mod = translate_device(name, content)
            mods.append(mod)
        elif content['category'] == 'abstract':
            mod = translate_abstract(name, content)
            mods.append(mod)
        elif content['category'] == "connection":
            if content['type'] == 'data':
                recv_num = len(content['target'])
                if recv_num not in dataBuffers:
                    dataBuffers[recv_num] = get_databuffer_module(recv_num)
        elif content['category'] == "bus":
            bus = translate_bus(name, content, jsoninfo)
            buses.append(bus)
        elif content['category'] == "processor":
            # processor use for change protocal, remain to be done
            continue
        else:
            raise NotImplementedError

    # Copy files that are the same for each system
    def copy_file(filename):
        with open(os.path.join("./aadl2hcsp/hcsp", filename), 'r') as f1:
            with open(os.path.join(output, filename), 'w') as f2:
                f2.write(f1.read())

    copy_file("ACT_aperiodic.txt")
    copy_file("ACT_periodic.txt")
    copy_file("BusEventBuffer.txt")
    copy_file("EventBuffer.txt")
    copy_file("SchedulerHPF.txt")

    # Generate files that are different for each system
    with open(os.path.join(output, 'other_modules.txt'), 'w') as f:
        f.write("%type: module\n\n")
        for mod in mods:
            f.write(mod.export())
            f.write('\n\n')

    with open(os.path.join(output, 'DataBuffer.txt'), 'w') as f:
        f.write("%type: module\n\n")
        for dataBuffer in dataBuffers.values():
            f.write(dataBuffer.export())
            f.write('\n\n')

    with open(os.path.join(output, 'Bus.txt'), 'w') as f:
        f.write("%type: module\n\n")
        for bus in buses:
            f.write(bus.export())
            f.write('\n\n')

    with open(os.path.join(output, 'system.txt'), 'w') as f:
        f.write("%type: module\n")
        f.write("import other_modules\n")
        f.write("import SchedulerHPF\n")
        f.write("import ACT_periodic\n")
        f.write("import ACT_aperiodic\n")
        f.write("import DataBuffer\n")
        f.write("import EventBuffer\n")
        f.write("import Bus\n")
        f.write("import BusEventBuffer\n\n")
        f.write("system\n\n")
        f.write(str(module.HCSPSystem(translate_system(jsoninfo))))
        f.write("\n\nendsystem")
