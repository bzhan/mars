"""Obtain submodules in the AADL to HCSP translation."""

from ss2hcsp.sl.get_hcsp import translate_continuous
from ss2hcsp.hcsp.expr import AConst, AVar, RelExpr, conj, disj, true_expr
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.module import HCSPModule


def get_bus_module(name, thread_ports, device_ports, latency):
    """
    :param name: bus name
    :param thread_ports: {thread_name: {port_name: port_type (out data or out event)}}
    :param device_ports: {device_name: {port_name: port_type (out data or out event)}}
    :param latency: ms
    :return: a module BUS(name)
    """

    reqBus_hps = list()
    unblock_hps = list()
    # io_comms = list()
    for sender, ports in thread_ports.items():
        reqBus = hp.ParaInputChannel(ch_name="reqBus", paras=[sender], is_str=True)
        get_datas = list()
        put_datas = list()
        get_events = list()
        put_events = list()
        init_events = list()
        transfer = list()
        for port_name, port_type in ports.items():
            if port_type == "out data":
                get_datas.append(hp.ParaInputChannel(ch_name="outputs", paras=[sender, port_name],
                                                     var_name=port_name, is_str=True))
                put_datas.append(hp.ParaOutputChannel(ch_name="outputs", paras=[name, port_name],
                                                      expr=AVar(port_name), is_str=True))
            elif port_type == "out event":
                get_events.append(hp.ParaInputChannel(ch_name="outputs", paras=[sender, port_name],
                                                      var_name=port_name, is_str=True))
                put_events.append(hp.ParaOutputChannel(ch_name="outputs", paras=[name, port_name],
                                                       expr=AVar(port_name), is_str=True))
                init_events.append(hp.Assign(var_name=port_name, expr=AConst("")))
            else:
                raise RuntimeError("port type must be either out data or out event!")
        if get_datas:
            get_datas = hp.Sequence(*get_datas) if len(get_datas) >= 2 else get_datas[0]
            transfer.append(get_datas)
        if init_events:
            init_events = hp.Sequence(*init_events) if len(init_events) >= 2 else init_events[0]
            transfer.append(init_events)
            transfer.append(hp.Assign(var_name="_freeBus", expr=AConst(0)))
        if get_events:
            io_comms = list()
            io_comms.extend([(event, hp.Skip()) for event in get_events])
            io_comms.append((hp.ParaInputChannel(ch_name="freeBus", paras=[sender]),
                             hp.Assign(var_name="_freeBus", expr=AConst(1))))
            get_events = hp.SelectComm(*io_comms)
            loop_cond = RelExpr("==", AVar("_freeBus"), AConst(0))
            get_events = hp.Loop(constraint=loop_cond, hp=get_events)
            transfer.append(get_events)
        transfer.append(hp.Var("BLOCK_by_"+sender))
        if put_events:
            cond_hps = list()
            cond_hps.extend([hp.Condition(cond=RelExpr("!=", event.expr, AConst("")), hp=event)
                             for event in put_events])
            put_events = hp.Sequence(*cond_hps) if len(cond_hps) >= 2 else cond_hps[0]
            transfer.append(put_events)
        if put_datas:
            put_datas = hp.Sequence(*put_datas) if len(put_datas) >= 2 else put_datas[0]
            transfer.append(put_datas)
        assert len(transfer) >= 2
        transfer = hp.Sequence(*transfer)
        reqBus_hps.append((reqBus, transfer))
        unblock_hps.append((hp.ParaOutputChannel(ch_name="unblock", paras=[sender], is_str=True), hp.Skip()))

    for sender, ports in device_ports.items():
        get_datas = list()
        put_datas = list()
        get_events = list()
        for port_name, port_type in ports.items():
            if port_type == "out data":
                get_datas.append(hp.ParaInputChannel(ch_name="outputs", paras=[sender, port_name],
                                                     var_name=port_name, is_str=True))
                put_datas.append(hp.ParaOutputChannel(ch_name="outputs", paras=[name, port_name],
                                                      expr=AVar(port_name), is_str=True))
            elif port_type == "out event":
                get_events.append(hp.ParaInputChannel(ch_name="inputs", paras=[name, port_name],
                                                      var_name="event", is_str=True))
            else:
                raise RuntimeError("port type must be either out data or out event!")
        if get_datas:
            reqBus = get_datas[0]
            transfer = list()
            transfer.extend(get_datas[1:])
            transfer.append(hp.Var("BLOCK"))
            transfer.extend(put_datas)
            transfer = hp.Sequence(*transfer) if len(transfer) >= 2 else transfer[0]
            reqBus_hps.append((reqBus, transfer))
        if get_events:
            for get_event in get_events:
                put_event = hp.ParaOutputChannel(ch_name="outputs", paras=get_event.paras,
                                                 expr=get_event.var_name, is_str=True)
                transfer = hp.Sequence(hp.Var("BLOCK"), put_event)
                reqBus_hps.append((get_event, transfer))
    io_comms = list()
    io_comms.extend(reqBus_hps)
    io_comms.extend(unblock_hps)
    assert len(io_comms) >= 1
    bus_hcsp = hp.Loop(hp.SelectComm(*io_comms)) if len(io_comms) >= 2\
        else hp.Loop(hp.Sequence(io_comms[0][0], io_comms[0][1]))

    # Get procedures of BLOCK and BLOCK_by_thread
    procedures = list()
    io_comms = [(hp.ParaOutputChannel(ch_name="block", paras=[thread], is_str=True), hp.Skip())
                for thread in thread_ports.keys()]
    reset_t = hp.Assign(var_name="t", expr=AConst(0))
    if len(io_comms) >= 1:
        eqs = [("t", AConst(1))]
        constraint = RelExpr("<", AVar("t"), AConst(latency))
        ode = hp.ODE_Comm(eqs=eqs, constraint=constraint, io_comms=io_comms)
        ode_loop = hp.Loop(constraint=constraint, hp=ode)
        procedures.append(hp.Procedure(name="BLOCK", hp=hp.Sequence(reset_t, ode_loop)))
    else:
        procedures.append(hp.Procedure(name="BLOCK", hp=hp.Wait(AConst(latency))))
    for i in range(len(io_comms)):
        thread = io_comms[i][0].paras[0]
        if len(io_comms) >= 2:
            ode = hp.ODE_Comm(eqs=eqs, constraint=constraint, io_comms=io_comms[:i]+io_comms[i+1:])
            ode_loop = hp.Loop(constraint=constraint, hp=ode)
            procedures.append(hp.Procedure(name="BLOCK_by_"+thread, hp=hp.Sequence(reset_t, ode_loop)))
        else:
            procedures.append(hp.Procedure(name="BLOCK_by_"+thread, hp=hp.Wait(AConst(latency))))

    return HCSPModule(name="Bus_"+name, code=bus_hcsp, procedures=procedures)


def get_databuffer_module(recv_num=1):
    init_x = hp.Assign(var_name="x", expr=AConst(0))
    init_data = hp.Assign(var_name="data", expr=AVar("init_value"))
    paras = ["send", "out_port"]
    io_comms = [(hp.ParaInputChannel(ch_name="outputs", paras=paras[-2:], var_name="data"), hp.Skip())]
    for i in range(recv_num):
        paras.append("recv"+str(i))
        paras.append("in_port"+str(i))
        io_comms.append((hp.ParaOutputChannel(ch_name="inputs", paras=paras[-2:], expr=AVar("data")), hp.Skip()))
    paras.append("init_value")
    transfer = hp.Loop(hp.ODE_Comm(eqs=[("x", AConst(0))], io_comms=io_comms, constraint=true_expr))

    return HCSPModule(name="DataBuffer" + str(recv_num),
                      params=paras,
                      code=hp.Sequence(init_x, init_data, transfer))


def get_continuous_module(name, ports, inputvalues, continuous_diagram, outputs):
    """
    ports: {port_name: (var_name, port_type)}
    """
    init_hps, equations, constraints, _, _, _ = translate_continuous(continuous_diagram)
    assert isinstance(init_hps[0], hp.Assign) and init_hps[0].var_name.name == "tt" and init_hps[0].expr.value == 0
    assert equations[0][0] == "tt" and equations[0][1].value == 1
    init_hps = init_hps[1:]
    equations = equations[1:]

    in_comms = list()
    out_comms = list()
    recv_flags = list()
    send_flags = list()
    for port_name, (var_name, port_type) in ports.items():
        if port_type == "in data":
            recv_flags.append(name + "_" + port_name)
            init_hps.append(hp.Assign(var_name=recv_flags[-1], expr=AConst(0)))
            in_comms.append((hp.ParaInputChannel(ch_name="outputs", paras=[name, port_name], var_name=var_name,
                                                 is_str=True),
                             hp.Assign(var_name=recv_flags[-1], expr=AConst(1))))
        elif port_type == "out data":
            send_flags.append(name + "_" + port_name)
            init_hps.append(hp.Assign(var_name=send_flags[-1], expr=AConst(0)))
            out_comms.append((hp.ParaOutputChannel(ch_name="inputs", paras=[name, port_name], expr=AVar(var_name),
                                                   is_str=True),
                              hp.Assign(var_name=send_flags[-1], expr=AConst(1))))
        else:
            raise RuntimeError("Not implemented!")
    for port_name ,(var_name, val) in inputvalues.items():
        init_hps.append(hp.Assign(var_name=var_name, expr=AConst(val)))
    init_hps = hp.Sequence(*init_hps) if len(init_hps) >= 2 else init_hps[0]

    assert send_flags
    assert len(send_flags) == len(out_comms)
    send_hp = out_comms[0][0]
    if len(send_flags) >= 2:
        loop_conds = [RelExpr("==", AVar(send_flag), AConst(0)) for send_flag in send_flags]
        loop_conds = disj(*loop_conds)
        send_hp = hp.Loop(constraint=loop_conds, hp=hp.SelectComm(*out_comms))

    assert recv_flags
    assert len(recv_flags) == len(in_comms)
    recv_hp = in_comms[0][0]
    if len(recv_flags) >= 2:
        loop_conds = [RelExpr("==", AVar(recv_flag), AConst(0)) for recv_flag in recv_flags]
        loop_conds = disj(*loop_conds)
        recv_hp = hp.Loop(constraint=loop_conds, hp=hp.SelectComm(*in_comms))

    io_comms = list()
    io_comms.extend([(in_comm, hp.Skip()) for in_comm, _ in in_comms])
    io_comms.extend([(out_comm, hp.Skip()) for out_comm, _ in out_comms])
    ode = hp.ODE_Comm(eqs=equations, constraint=conj(*constraints), io_comms=io_comms)
    ode_loop = hp.Loop(ode)

    code = hp.Sequence(init_hps, send_hp, recv_hp, ode_loop)

    return HCSPModule(name=name, code=code, outputs=outputs)
