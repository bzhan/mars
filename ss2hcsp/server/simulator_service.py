from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser


def process_multi(hcsp_programs: dict, debug: bool = False):
    """
    Execute the process for multiple hcsp pograms
    :param debug: debug mode switch
    :param hcsp_programs: a dict, {"program_id_1", :{"code":..., "state":..., "reason":..}}
    :return: the code, state and reason for every hcsp program.
    :return: returns a dict: {"program_id_1": {"new_code": ..., "new_state":..., "reason":...}...}
    """

    reasons = {}
    result_hcsp_programs = {}

    # parse hcsp program

    for program_id in hcsp_programs.keys():
        code, state = hcsp_programs[program_id]['code'], hcsp_programs[program_id]['state']
        code = parser.hp_parser.parse(code)
        hcsp_programs[program_id]['code'] = code
        hcsp_programs[program_id]['state'] = state

    for program_id in hcsp_programs.keys():
        old_code, old_state = hcsp_programs[program_id]['code'], hcsp_programs[program_id]['state']
        new_code, reason = simulator.exec_process(old_code, old_state)
        new_state = old_state
        reasons[program_id] = reason
        result_hcsp_programs[program_id] = {"code": new_code, "state": new_state, "reason": reason}

    # Find matching communication
    id_in, id_out, ch_name = None, None, None

    for program_id_1 in reasons.keys():
        reason1, rest1 = reasons[program_id_1]
        for program_id_2 in reasons.keys():
            reason2, rest2 = reasons[program_id_2]
            if reason1 == "comm" and reason2 == "comm":
                for ch_name1, dir1 in rest1:
                    for ch_name2, dir2 in rest2:
                        if ch_name1 == ch_name2 and dir1 == "!" and dir2 == "?":
                            id_out, id_in, ch_name = program_id_1, program_id_2, ch_name1

    if id_in is None:
        # No matching communication. Find minimum delay among
        # the processes.
        min_delay = None
        for reason, rest in reasons.values():
            if reason == "delay":
                if min_delay is None or min_delay > rest:
                    min_delay = rest

        # If no delay is possible, the system is in a deadlock
        if min_delay is None:
            for program_id in result_hcsp_programs:
                result_hcsp_programs[program_id]["reason"] = ("deadlock", None)
            return result_hcsp_programs

        # Otherwise, execute the delay.
        if debug:
            print("\nDelay for %s seconds" % str(min_delay))
        # trace.append("delay %s" % str(min_delay))
        for program_id in result_hcsp_programs.keys():
            new_code = simulator.exec_delay(result_hcsp_programs[program_id]['code'],
                                            result_hcsp_programs[program_id]['state'],
                                            min_delay)
            result_hcsp_programs[program_id] = {"code": new_code,
                                                "state": result_hcsp_programs[program_id]['state'],
                                                "reason": ("execute_delay", min_delay)}
    else:
        # If there is a matching communication, perform the
        # communication.
        if debug:
            print("\nCommunication from %d to %d on %s" % (id_out, id_in, ch_name))
        code_in, state_in = result_hcsp_programs[id_in]['code'], result_hcsp_programs[id_in]['state']
        code_out, state_out = result_hcsp_programs[id_out]['code'], result_hcsp_programs[id_out]['state']
        new_code_out, val = simulator.exec_output_comm(code_out, state_out, ch_name)
        new_code_in = simulator.exec_input_comm(code_in, state_in, ch_name, val)
        result_hcsp_programs[id_in] = {"code": new_code_in,
                                       "state": result_hcsp_programs[id_in]['state'],
                                       "reason": ("comm_in", {"ch_name": ch_name, "value": val})}
        result_hcsp_programs[id_out] = {"code": new_code_out,
                                        "state": result_hcsp_programs[id_out]['state'],
                                        "reason": ("comm_out", {"ch_name": ch_name, "value": val})}
        if debug:
            print("... %s transfered, with result")


    return result_hcsp_programs


def step_multi(hcsp_programs: dict, debug: bool = False):
    """
        Execute the step for multiple hcsp pograms
        :param debug: debug mode switch
        :param hcsp_programs: a dict, {"program_id_1", :{"code":..., "state":..., "reason":..}}
        :return: the code, state and reason for every hcsp program.
        :return: returns a dict: {"program_id_1": {"new_code": ..., "new_state":..., "reason":...}...}
        """

    reasons = {}
    result_hcsp_programs = {}

    # parse hcsp program

    for program_id in hcsp_programs.keys():
        code, state = hcsp_programs[program_id]['code'], hcsp_programs[program_id]['state']
        code = parser.hp_parser.parse(code)
        hcsp_programs[program_id]['code'] = code
        hcsp_programs[program_id]['state'] = state

    for program_id in hcsp_programs.keys():
        old_code, old_state = hcsp_programs[program_id]['code'], hcsp_programs[program_id]['state']
        reason, rest = simulator.exec_step(old_code, old_state)
        if reason == "step":
            # do step
            new_code = rest
            reason = (reason, None)
        else:
            # no step, delay, comm, etc
            new_code = old_code
            reason = (reason, rest)
        new_state = old_state
        reasons[program_id] = reason
        result_hcsp_programs[program_id] = {"code": new_code, "state": new_state, "reason": reason}

    all_not_step = True
    for program_id in reasons.keys():
        reason, rest = reasons[program_id]
        if reason == "step":
            all_not_step = False
            break
    if all_not_step:
        # Find matching communication
        id_in, id_out, ch_name = None, None, None

        for program_id_1 in reasons.keys():
            reason1, rest1 = reasons[program_id_1]
            for program_id_2 in reasons.keys():
                reason2, rest2 = reasons[program_id_2]
                if reason1 == "comm" and reason2 == "comm":
                    for ch_name1, dir1 in rest1:
                        for ch_name2, dir2 in rest2:
                            if ch_name1 == ch_name2 and dir1 == "!" and dir2 == "?":
                                id_out, id_in, ch_name = program_id_1, program_id_2, ch_name1

        if id_in is None:
            # No matching communication. Find minimum delay among
            # the processes.
            min_delay = None
            for reason, rest in reasons.values():
                if reason == "delay":
                    if min_delay is None or min_delay > rest:
                        min_delay = rest

            # If no delay is possible, the system is in a deadlock
            if min_delay is None:
                for program_id in result_hcsp_programs:
                    result_hcsp_programs[program_id]["reason"] = ("deadlock", None)
                return result_hcsp_programs

            # Otherwise, execute the delay.
            if debug:
                print("\nDelay for %s seconds" % str(min_delay))
            # trace.append("delay %s" % str(min_delay))
            for program_id in result_hcsp_programs.keys():
                new_code = simulator.exec_delay(result_hcsp_programs[program_id]['code'],
                                                result_hcsp_programs[program_id]['state'],
                                                min_delay)
                result_hcsp_programs[program_id] = {"code": new_code,
                                                    "state": result_hcsp_programs[program_id]['state'],
                                                    "reason": ("execute_delay", min_delay)}
        else:
            # If there is a matching communication, perform the
            # communication.
            if debug:
                print("\nCommunication from %d to %d on %s" % (id_out, id_in, ch_name))
            code_in, state_in = result_hcsp_programs[id_in]['code'], result_hcsp_programs[id_in]['state']
            code_out, state_out = result_hcsp_programs[id_out]['code'], result_hcsp_programs[id_out]['state']
            new_code_out, val = simulator.exec_output_comm(code_out, state_out, ch_name)
            new_code_in = simulator.exec_input_comm(code_in, state_in, ch_name, val)
            result_hcsp_programs[id_in] = {"code": new_code_in,
                                           "state": result_hcsp_programs[id_in]['state'],
                                           "reason": ("comm_in", {"ch_name": ch_name, "value": val})}
            result_hcsp_programs[id_out] = {"code": new_code_out,
                                            "state": result_hcsp_programs[id_out]['state'],
                                            "reason": ("comm_out", {"ch_name": ch_name, "value": val})}
            if debug:
                print("... %s transfered, with result")

    return result_hcsp_programs
