# New version of translator from JSON to HCSP

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint


def time_str_to_int(time_str):
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
    dis[name]?;
    @INPUT;
    t := 0; entered := 0; state := "ready"
elif state == "ready" then
    reqProcessor[sid][name]!prior;
    <t_dot = 1 & t < DL> |> [] (run[sid][name]? --> state := "running");
    t == DL ->
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

def translate_thread(name, info):
    """Translate to HCSP module for threads."""
    mod = parser.module_parser.parse(thread_template)

    # Arguments to module
    max_c = time_str_to_int(info['Compute_Execution_Time'])
    DL = time_str_to_int(info['Deadline'])
    priority = info['priority']
    mod_inst = module.HCSPModuleInst("EXE" + name, "EXE", [
        expr.AConst(0),
        expr.AConst(name),
        expr.AConst(max_c),
        expr.AConst(DL),
        expr.AConst(priority)])
    hp_info = mod_inst.generateInst(mod)

    # Input procedure
    def get_input(port, var_name):
        return hcsp.InputChannel(hcsp.Channel("inputs", (name, port)), var_name)
    
    def get_event_input(event_port, event_val):
        return (hcsp.InputChannel(hcsp.Channel("dis", (name, event_port))),
                hcsp.Assign("event", expr.AConst(event_val)))

    if info['dispatch_protocol'] == 'periodic':
        inputs = [get_input(port, port_info['var'])
                  for port, port_info in info['input'].items()]
        input_hp = hcsp.Sequence(*inputs)
    elif info['dispatch_protocol'] == 'aperiodic':
        io_comms = [get_event_input(event_port, event_val)
                    for event_port, event_val in info['event_input'].items()]
        input_hp = hcsp.SelectComm(*io_comms)
    else:
        raise NotImplementedError

    # Output procedure
    def get_output(port, var_name):
        return hcsp.OutputChannel(hcsp.Channel("outputs", (name, port)), hcsp.AVar(var_name))
    outputs = [get_output(port, var_name) for port, var_name in info['output'].items()]

    inst = {
        "INIT": parser.hp_parser.parse(info['initialization']),
        "INPUT": input_hp,
        "DISCRETE_COMPUTATION": parser.hp_parser.parse(info['discrete_computation']),
        "OUTPUT": hcsp.Sequence(*outputs)
    }
    hp = hcsp.HCSP_subst(hp_info.hp, inst)
    new_mod = module.HCSPModule("EXE_" + name, [], [], hp)
    return new_mod

def translate_device(name, info):
    """Translate to HCSP module for devices."""
    if info['impl'] == 'Simulink':
        hp = parser.hp_parser.parse(info['computation'])
        new_mod = module.HCSPModule("DEVICE_" + name, [], [], hp)
        return new_mod

    elif info['impl'] == 'Channel':
        # Input procedure
        def get_input(port, var_name):
            return hcsp.InputChannel(hcsp.Channel("inputs", (name, port)), var_name)
        inputs = [get_input(port, port_info['var'])
                  for port, port_info in info['input'].items()]

        # Output procedure
        def get_output(port, var_name):
            return hcsp.OutputChannel(hcsp.Channel("outputs", (name, port)), hcsp.AVar(var_name))
        outputs = [get_output(port, var_name) for port, var_name in info['output'].items()]

        # Wait
        delay = time_str_to_int(info['period'])
        wait_hp = hcsp.Wait(expr.AConst(delay))

        hp = hcsp.Loop(hcsp.Sequence(*(inputs + outputs + [wait_hp])))
        new_mod = module.HCSPModule("DEVICE_" + name, [], [], hp)
        return new_mod

    else:
        raise NotImplementedError

def translate_abstract(name, info):
    """Translate to HCSP module for abstract components (plants)"""
    if info['impl'] == 'Simulink':
        hp = parser.hp_parser.parse(info['code'])
        new_mod = module.HCSPModule("PHY_" + name, [], info['display'], hp)
        return new_mod

    else:
        raise NotImplementedError

def translate_model(json_info):
    """Overall translation"""
    # First, collect input and output ports
    # inputs - mapping from input port name to component name and type ("DATA" or "EVENT")
    # outputs - mapping from output port name to component name
    inputs = dict()
    outputs = dict()

    for name, info in json_info.items():
        if 'input' in info:
            for in_port in info['input']:
                if in_port in inputs:
                    raise AssertionError("Duplicate in_port %s in %s" % (in_port, name))
                inputs[in_port] = (name, "DATA", info['input'][in_port]['val'])

        if 'event_input' in info:
            for in_port in info['event_input']:
                if in_port in inputs:
                    raise AssertionError("Duplicate in_port %s in %s" % (in_port, name))
                inputs[in_port] = (name, "EVENT", None)

        if 'output' in info:
            for out_port in info['output']:
                if out_port in outputs:
                    raise AssertionError("Duplicate out_port %s in %s" % (out_port, name))
                outputs[out_port] = name

    # inputs and outputs should have exactly the same keys
    for in_port in inputs:
        if in_port not in outputs:
            raise AssertionError("%s is an in_port but not an out_port" % in_port)
    for out_port in outputs:
        if out_port not in inputs:
            raise AssertionError("%s is an out_port but not an in_port" % out_port)

    # Print the ports
    for in_port in inputs:
        in_comp, typ, init_val = inputs[in_port]
        out_comp = outputs[in_port]
        if typ == 'DATA':
            print("DataBuffer(%s, %s, %s, %s, %s)" % (out_comp, in_port, in_comp, in_port, init_val))
        elif typ == 'EVENT':
            print("EventBuffer(%s, %s, %s, %s)" % (out_comp, in_port, in_comp, in_port))
        else:
            raise NotImplementedError
