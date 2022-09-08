from ss2hcsp.sl.get_hcsp import new_translate_discrete, new_translate_continuous
from ss2hcsp.hcsp.expr import AConst, AVar, RelExpr, conj, disj, true_expr
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.module import HCSPModule


def get_thread_module(name, ports, discrete_diagram, deadline, max_et, prior=0, processor=0, reqResources=None):
    """
    :param name: the name of the thread
    :param ports: the ports of the thread in the form of {port_name: port_type}
    :param discrete_diagram: the discrete Simulink diagram of the thread
    :param deadline: the deadline of the thread, and deadline <= period
    :param max_et: maximal execution time
    :param prior: the priority of the thread
    :param processor: the thread is bound to processor
    :param reqResources: Resources required, like buses and so on
    :return: two HCSPs (modules) for the thread: Dispatch and Execution
    """

    init_hps, procedures, output_hps, update_hps, _ = new_translate_discrete(discrete_diagram)

    # Initialize the out-event port states
    init_hps.extend([hp.Assign(var_name=port_name, expr=AConst(0))
                     for port_name, port_type in ports.items() if port_type == "out event"])

    # Add state := "wait" and prior := ?? to the initialization list
    init_hps.extend([hp.Assign(var_name="state", expr=AConst("wait")),
                     hp.Assign(var_name="prior", expr=AConst(prior))])
    init_hps = hp.Sequence(*init_hps)
    # if state == "wait" then ...
    cond_wait = RelExpr("==", AVar("state"), AConst("wait"))
    hp_wait = list()
    if any(port_type == "in event" for port_type in ports.values()):
        input_events = [(hp.ParaInputChannel(ch_name="dis", paras=[name, port_name], var_name="event"), hp.Skip())
                        for port_name, port_type in ports.items() if port_type == "in event"]
        input_events = hp.SelectComm(*input_events) if len(input_events) >= 2 else input_events[0][0]
        hp_wait.append(input_events)
    else:
        hp_wait.append(hp.ParaInputChannel(ch_name="dis", paras=[name]))
    if any(port_type == "in data" for port_type in ports.values()):
        input_datas = [hp.ParaInputChannel(ch_name="inputs", paras=[name, port_name], var_name=port_name)
                       for port_name, port_type in ports.items() if port_type == "in data"]
        input_datas = hp.Sequence(*input_datas) if len(input_datas) >= 2 else input_datas[0]
        hp_wait.append(input_datas)
    hp_wait.extend([hp.Assign(var_name="t", expr=AConst(0)),
                    hp.Assign(var_name="entered", expr=AConst(0)),
                    hp.Assign(var_name="state", expr=AConst("ready"))])
    hp_wait = hp.Sequence(*hp_wait)
    # elif state == "ready" then ...
    cond_ready = RelExpr("==", AVar("state"), AConst("ready"))
    hp_ready = list()
    hp_ready.append(hp.ParaOutputChannel(ch_name="reqProcessor", paras=[processor, name], expr=AVar("prior")))
    hp_ready.append(hp.ODE_Comm(eqs=[("t", AConst(1))], constraint=RelExpr("<", AVar("t"), AConst(deadline)),
                                io_comms=[(hp.ParaInputChannel(ch_name="run", paras=[processor, name]),
                                           hp.Assign(var_name="state", expr=AConst("running")))]
                                )
                    )
    hp_ready.append(hp.Condition(cond=RelExpr("==", AVar("t"), AConst(deadline)),
                                 hp=hp.SelectComm((hp.ParaOutputChannel(ch_name="exit", paras=[processor, name]),
                                                   hp.Assign(var_name="state", expr=AConst("wait"))),
                                                  (hp.ParaInputChannel(ch_name="run", paras=[processor, name]),
                                                   hp.Assign(var_name="state", expr=AConst("running")))
                                                  )
                                 )
                    )
    hp_ready = hp.Sequence(*hp_ready)
    # elif state == "running"
    cond_running = RelExpr("==", AVar("state"), AConst("running"))
    #   entered == 0 -> ...
    entered0 = RelExpr("==", AVar("entered"), AConst(0))
    entered0_hp = list()
    entered0_hp.append(hp.Assign(var_name="c", expr=AConst(0)))
    #       The main hcsp of the thread is output_hps + updata_hps
    entered0_hp.extend([output_hp.hp for output_hp in output_hps])
    entered0_hp.extend([update_hp.hp for update_hp in update_hps])
    entered0_hp.append(hp.Assign(var_name="entered", expr=AConst(1)))
    entered0_hp = hp.Condition(cond=entered0, hp=hp.Sequence(*entered0_hp))
    #   entered == 1 -> ...
    entered1 = RelExpr("==", AVar("entered"), AConst(1))
    entered1_hp = list()
    entered1_hp.append(hp.ODE_Comm(eqs=[("t", AConst(1)), ("c", AConst(1))],
                                   constraint=conj(RelExpr("<", AVar("c"), AConst(max_et)),
                                                   RelExpr("<", AVar("t"), AConst(deadline))),
                                   io_comms=[(hp.ParaInputChannel(ch_name="preempt", paras=[processor, name]),
                                              hp.Assign(var_name="state", expr=AConst("ready")))
                                             ]
                                   )
                       )
    # state == "running" -> ...
    #   if c == max_et then ...
    cond_max_et = RelExpr("==", AVar("c"), AConst(max_et))

    _outputs = list()
    if any(port_type == "out event" for port_type in ports.values()):
        output_events = [hp.Condition(cond=RelExpr("==", AVar(port_name), AConst(1)),
                                      hp=hp.Sequence(hp.Assign(var_name=port_name, expr=AConst(0)),
                                                     hp.ParaOutputChannel(ch_name="outputs",
                                                                          paras=[name, port_name])))
                         for port_name, port_type in ports.items() if port_type == "out event"]
        output_events = hp.Sequence(*output_events) if len(output_events) >= 2 else output_events[0]
        _outputs.append(output_events)
    if any(port_type == "out data" for port_type in ports.values()):
        output_datas = [hp.ParaOutputChannel(ch_name="outputs", paras=[name, port_name], expr=AVar(port_name))
                        for port_name, port_type in ports.items() if port_type == "out data"]
        output_datas = hp.Sequence(*output_datas) if len(output_datas) >= 2 else output_datas[0]
        _outputs.append(output_datas)
    assert len(_outputs) >= 1
    _outputs = hp.Sequence(*_outputs) if len(_outputs) >= 2 else _outputs[0]

    to_wait = hp.SelectComm((hp.ParaInputChannel(ch_name="preempt", paras=[processor, name]),
                             hp.Assign(var_name="state", expr=AConst("wait"))),
                            (hp.ParaOutputChannel(ch_name="free", paras=[processor, name]),
                             hp.Assign(var_name="state", expr=AConst("wait")))
                            )
    hp_max_et = hp.Sequence(_outputs, to_wait)
    if reqResources:
        # At present, we assume that BUS is the only required resource.
        assert reqResources == "bus"
        freeResources = hp.ParaOutputChannel(ch_name="freeBus", paras=[name])
        hp_max_et = hp.Sequence(_outputs, freeResources, to_wait)
        block_hp = hp.SelectComm((hp.ParaInputChannel(ch_name="preempt", paras=[processor, name]),
                                  hp.Assign(var_name="state", expr=AConst("await"))),
                                 (hp.ParaOutputChannel(ch_name="free", paras=[processor, name]),
                                  hp.Assign(var_name="state", expr=AConst("await")))
                                 )
        hp_max_et = hp.SelectComm((hp.ParaOutputChannel(ch_name="reqBus", paras=[name]), hp_max_et),
                                  (hp.ParaInputChannel(ch_name="block", paras=[name]), block_hp))
    hp_running = hp.ITE(if_hps=[(cond_max_et, hp_max_et)], else_hp=to_wait)
    hp_running = hp.Condition(cond=cond_running, hp=hp_running)
    entered1_hp.append(hp_running)
    entered1_hp = hp.Condition(cond=entered1, hp=hp.Sequence(*entered1_hp))
    hp_running = hp.Sequence(entered0_hp, entered1_hp)
    # else (state == "await")
    unblock_hp = hp.ODE_Comm(eqs=[("t", AConst(1))], constraint=RelExpr("<", AVar("t"), AConst(deadline)),
                             io_comms=[(hp.ParaInputChannel(ch_name="unblock", paras=[name]),
                                        hp.Assign(var_name="state", expr=AConst("ready")))]
                             )
    time_out = hp.Condition(cond=RelExpr("==", AVar("t"), AConst(deadline)),
                            hp=hp.Assign(var_name="state", expr=AConst("wait"))
                            )
    hp_await = hp.Sequence(unblock_hp, time_out)

    # Get EXE_thread
    # execute_thead = hp.HCSP()
    if reqResources:
        execute_thead = hp.ITE(if_hps=[(cond_wait, hp_wait), (cond_ready, hp_ready), (cond_running, hp_running)],
                               else_hp=hp_await)
    else:
        execute_thead = hp.ITE(if_hps=[(cond_wait, hp_wait), (cond_ready, hp_ready)],
                               else_hp=hp_running)
    return HCSPModule(name=name,
                      code=hp.Sequence(init_hps, hp.Loop(execute_thead)),
                      outputs=set(port_name for port_name, port_type in ports.items() if port_type == "out data"),
                      procedures=procedures)
    # return execute_thead


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
    procesures = list()
    io_comms = [(hp.ParaOutputChannel(ch_name="block", paras=[thread], is_str=True), hp.Skip())
                for thread in thread_ports.keys()]
    reset_t = hp.Assign(var_name="t", expr=AConst(0))
    if len(io_comms) >= 1:
        eqs = [("t", AConst(1))]
        constraint = RelExpr("<", AVar("t"), AConst(latency))
        ode = hp.ODE_Comm(eqs=eqs, constraint=constraint, io_comms=io_comms)
        ode_loop = hp.Loop(constraint=constraint, hp=ode)
        procesures.append(hp.Procedure(name="BLOCK", hp=hp.Sequence(reset_t, ode_loop)))
    else:
        procesures.append(hp.Procedure(name="BLOCK", hp=hp.Wait(AConst(latency))))
    for i in range(len(io_comms)):
        thread = io_comms[i][0].paras[0]
        if len(io_comms) >= 2:
            ode = hp.ODE_Comm(eqs=eqs, constraint=constraint, io_comms=io_comms[:i]+io_comms[i+1:])
            ode_loop = hp.Loop(constraint=constraint, hp=ode)
            procesures.append(hp.Procedure(name="BLOCK_by_"+thread, hp=hp.Sequence(reset_t, ode_loop)))
        else:
            procesures.append(hp.Procedure(name="BLOCK_by_"+thread, hp=hp.Wait(AConst(latency))))

    return HCSPModule(name="Bus_"+name, code=bus_hcsp, procedures=procesures)


def get_databuffer_module(recv_num=1):
    init_hp = hp.Assign(var_name="data", expr=AVar("init_value"))
    paras = ["send", "out_port"]
    io_comms = [(hp.ParaInputChannel(ch_name="outputs", paras=paras[-2:], var_name="data"), hp.Skip())]
    for i in range(recv_num):
        paras.append("recv"+str(i))
        paras.append("in_port"+str(i))
        io_comms.append((hp.ParaOutputChannel(ch_name="inputs", paras=paras[-2:], expr=AVar("data")), hp.Skip()))
    paras.append("init_value")
    transfer = hp.Loop(hp.ODE_Comm(eqs=[("data", AConst(0))], io_comms=io_comms, constraint=true_expr))

    return HCSPModule(name="DataBuffer"+str(recv_num), params=paras, code=hp.Sequence(init_hp, transfer))


def get_continuous_module(name, ports, continuous_diagram, outputs):
    """
    ports: {port_name: (var_name, port_type)}
    """
    init_hps, equations, constraints, _, _, _ = new_translate_continuous(continuous_diagram)
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
