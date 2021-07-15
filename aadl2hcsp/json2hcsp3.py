# New version of translator from JSON to HCSP

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sl.get_hcsp import new_translate_discrete
from ss2hcsp.aadl.get_modules import get_continuous_module, get_bus_module
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
(
if state == "wait" then
    @INPUT;
    t := 0; entered := 0; state := "ready"
elif state == "ready" then
    reqProcessor[sid][name]!prior;
    <t_dot = 1 & t < DL> |> [] (run[sid][name]? --> state := "running");
    t == DL && state == "ready" ->
        (
        exit[sid][name]! --> state := "wait"
        $
        run[sid][name]? --> state := "running"
        )
else
    entered == 0 ->
    (
        c := 0;
        @DISCRETE_COMPUTATION;
        entered := 1
    );
    entered == 1 ->
    (
        <t_dot = 1, c_dot = 1 & c < max_c && t < DL> |> []
          (preempt[sid][name]? --> state := "ready");
        state == "running" ->
            (
            if c == max_c then
                @OUTPUT;
                (preempt[sid][name]? --> state := "wait" $ free[sid][name]! --> state := "wait")
            else
                (preempt[sid][name]? --> state := "wait" $ free[sid][name]! --> state := "wait")
            endif
            )
    )
endif
)**
end
endmodule
"""

thread_with_bus_template = """
module EXE(sid, name, max_c, DL, priority, bus):
begin
@INIT;
state := "wait"; prior := priority;
(
if state == "wait" then
    @INPUT;
    t := 0; entered := 0; state := "ready"
elif state == "ready" then
    reqProcessor[sid][name]!prior;
    <t_dot = 1 & t < DL> |> [] (run[sid][name]? --> state := "running");
    t == DL && state == "ready" ->
        (
        exit[sid][name]! --> state := "wait"
        $
        run[sid][name]? --> state := "running"
        )
elif state == "running" then
    entered == 0 ->
    (
        c := 0;
        @DISCRETE_COMPUTATION;
        entered := 1
    );
    entered == 1 ->
    (
        <t_dot = 1, c_dot = 1 & c < max_c && t < DL> |> []
          (preempt[sid][name]? --> state := "ready");
        state == "running" ->
            (
            if c == max_c then
                reqBus[name]! --> (@OUTPUT; (preempt[sid][name]? --> state := "wait" $ free[sid][name]! --> state := "wait"))
                $
                block[name]? --> (preempt[sid][name]? --> state := "await" $ free[sid][name]! --> state := "await")
            else
                (preempt[sid][name]? --> state := "wait" $ free[sid][name]! --> state := "wait")
            endif
            )
    )
else
    <t_dot = 1 & t < 0.005> |> [] (unblock["emerg_imp"]? --> state := "ready");
    t == 0.005 -> state := "wait"
endif
)**
end
endmodule
"""


def translate_thread(name, info, bus=None):
    """Translate to HCSP module for threads."""
    max_c = time_str_to_num(info['Compute_Execution_Time'])
    DL = time_str_to_num(info['Deadline'])
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
        input_dis = hcsp.InputChannel(hcsp.Channel("dis", (expr.AConst(name),)))
        inputs = [get_input(port, port_info['var'])
                  for port, port_info in info['input'].items()]
        input_hp = hcsp.Sequence(*([input_dis] + inputs))
    elif info['dispatch_protocol'] == 'aperiodic':
        io_comms = [get_event_input(event_port, event_val)
                    for event_port, event_val in info['event_input'].items()]
        input_hp = hcsp.SelectComm(*io_comms) if len(io_comms) >= 2 else io_comms[0][0]
    else:
        raise NotImplementedError

    # Output procedure
    def get_output(port, var_name):
        return hcsp.OutputChannel(hcsp.Channel("outputs", (expr.AConst(name), expr.AConst(port))), hcsp.AVar(var_name))
    outputs = [get_output(port, var_name) for port, var_name in info['output'].items()]

    # Discrete Computation
    def get_discrete_computation(location):
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        _init_hps, _procedures, _output_hps, _update_hps, _ =\
            new_translate_discrete(list(diagram.blocks_dict.values()))
        if len(_init_hps) >= 2:
            _init_hps = hcsp.Sequence(*_init_hps)
        elif len(_init_hps) == 1:
            _init_hps = _init_hps[0]
        else:
            _init_hps = ""
        _procedures = [hcsp.Procedure(name=_name, hp=_hcsp) for _name, _hcsp in _procedures]
        _hps = [_hcsp.hp for _hcsp in _output_hps + _update_hps]
        if len(_hps) >= 2:
            _hps = hcsp.Sequence(*_hps)
        elif len(_hps) == 1:
            _hps = _hps[0]
        else:
            _hps = hcsp.Skip()
        return _init_hps, _procedures, _hps

    def get_stateflow_computation(location):
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        _, _, charts, _, _, _, _, _ = diagram.seperate_diagram()
        assert len(charts) == 1
        converter = sf_convert.SFConvert(charts[0], chart_parameters=diagram.chart_parameters[charts[0].name])
        _init_hp = converter.get_init_proc()
        _dis_comp = converter.get_iteration()
        _procesures = []
        return _init_hp, _procesures, _dis_comp

    initlizations = list()
    if info['initialization']:
        initlizations.append(parser.hp_parser.parse(info['initialization']))
    if info['impl'] == "Simulink":
        init_hp, procesures, dis_comp = get_discrete_computation(location=info['discrete_computation'])
        if init_hp:
            initlizations.append(init_hp)
    elif info['impl'] == "Stateflow":
        init_hp, procesures, dis_comp = get_stateflow_computation(location=info['discrete_computation'])
        initlizations.append(init_hp)
    else:
        raise NotImplementedError

    inst = {
        "INIT": hcsp.Sequence(*initlizations) if initlizations else hcsp.Skip(),
        "INPUT": input_hp,
        "DISCRETE_COMPUTATION": dis_comp,
        "OUTPUT": hcsp.Sequence(*outputs)
    }
    hp = hcsp.HCSP_subst(hp_info.hp, inst)
    # new_mod = module.HCSPModule("EXE_" + name, [], [], hp)
    new_mod = module.HCSPModule(name="EXE_"+name, code=hp, procedures=procesures)
    return new_mod


def translate_device(name, info):
    """Translate to HCSP module for devices."""
    if info['impl'] == 'Simulink':
        hp = parser.hp_parser.parse(info['computation'])
        # new_mod = module.HCSPModule("DEVICE_" + name, [], [], hp)
        new_mod = module.HCSPModule(name="DEVICE_" + name, code=hp)
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
        outputs = [get_output(port, var_name) for port, var_name in info['output'].items()]

        # Wait
        delay = time_str_to_num(info['period'])
        wait_hp = hcsp.Wait(expr.AConst(delay))

        hp = hcsp.Loop(hcsp.Sequence(*(inputs + outputs + [wait_hp])))
        # new_mod = module.HCSPModule("DEVICE_" + name, [], [], hp)
        new_mod = module.HCSPModule(name="DEVICE_" + name, code=hp)
        return new_mod

    else:
        raise NotImplementedError


def translate_abstract(name, info):
    """Translate to HCSP module for abstract components (plants)"""
    if info['impl'] == 'Simulink':
        diagram = SL_Diagram(location=info['code'])
        _ = diagram.parse_xml()
        diagram.add_line_name()

        # get ports {port_name: port_type}
        ports = dict()
        for port_name, var_dict in info["input"].items():
            assert port_name not in ports
            ports[port_name] = (var_dict['var'], "in data")
        for port_name, var_name in info["output"].items():
            assert port_name not in ports
            ports[port_name] = (var_name, "out data")
        return get_continuous_module(name="PHY_"+name,
                                     ports=ports,
                                     continuous_diagram=list(diagram.blocks_dict.values()),
                                     outputs=info['display'])

    else:
        raise NotImplementedError


def translate_bus(name, info, json_info):
    latency = time_str_to_num(info['latency'])
    thread_ports = dict()
    device_ports = dict()
    for _info in json_info.values():
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


def translate_model(json_info):
    """Overall translation"""
    # Construct the components
    component_mod_insts = [module.HCSPModuleInst("scheduler", "SCHEDULLER_HPF", [expr.AConst(0)])]
    for name, info in json_info.items():
        if info['category'] == 'thread':
            if info['dispatch_protocol'] == 'periodic':
                component_mod_insts.append(module.HCSPModuleInst("ACT_" + name, "ACT_periodic", [
                    expr.AConst(name), expr.AConst(time_str_to_num(info['period']))
                ]))
            component_mod_insts.append(module.HCSPModuleInst(name, "EXE_" + name, []))

        elif info['category'] == 'device':
            component_mod_insts.append(module.HCSPModuleInst(name, "DEVICE_" + name, []))

        elif info['category'] == 'abstract':
            component_mod_insts.append(module.HCSPModuleInst(name, "PHY_" + name, []))

        elif info['category'] == 'connection':
            source = info['source']
            source_port = info['source_port']
            targets = info['targets']
            target_ports = info['target_ports']
            assert len(targets) == len(target_ports)

            if info['bus']:
                source = info['bus']
            args = [expr.AConst(source), expr.AConst(source_port)]

            for target, target_port in zip(targets, target_ports):
                args.append(expr.AConst(target))
                args.append(expr.AConst(target_port))
            if info['type'] == "data":
                args.append(expr.AConst(info['init_value']))
                component_mod_insts.append(module.HCSPModuleInst(name, "DataBuffer"+str(len(targets)), args))
            elif info['type'] == "event":
                assert len(targets) == 1
                component_mod_insts.append(module.HCSPModuleInst(name, "EventBuffer", args))
                if info['bus']:
                    component_mod_insts.append(module.HCSPModuleInst("busBuffer_"+name, "BusBuffer",
                                                                     [expr.AConst(info['source']),
                                                                      expr.AConst(source_port),
                                                                      expr.AConst(source),
                                                                      expr.AConst(source_port)]))
            else:
                raise NotImplementedError
        elif info['category'] == 'bus':
            component_mod_insts.append(module.HCSPModuleInst(name, "Bus_"+name, []))
        else:
            raise NotImplementedError

    return component_mod_insts

    # for mod_inst in component_mod_insts:
    #     print(mod_inst.export())
