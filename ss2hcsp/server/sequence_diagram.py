# Printing sequence diagram for a trace to a text file.


def print_sequence_diagram(trace):
    # First entry of trace contains all processes
    all_processes = sorted(trace[0]['ori_pos'].keys())

    # Mapping from process name to a list of events.
    # '|' represents no event for this process.
    events = dict()
    for process in all_processes:
        events[process] = [process]

    # List of ids
    ids = ['ID']

    num_events = 1
    def add_event(id, event, processes):
        nonlocal num_events
        num_events += 1
        ids.append(id)
        for process in all_processes:
            if process in processes:
                events[process].append(event)
            else:
                events[process].append('|')

    def add_io(id, event, inproc, outproc):
        nonlocal num_events
        num_events += 1
        ids.append(id)
        for process in all_processes:
            if process == inproc:
                events[process].append(event + '?')
            elif process == outproc:
                events[process].append(event + '!')
            else:
                events[process].append('|')

    for i, step in enumerate(trace[1:]):
        if step['type'] == 'log':
            add_event(i, step['str'], step['ori_pos'])
        elif step['type'] == 'comm':
            add_io(i, step['ch_name'], step['inproc'], step['outproc'])
        elif step['type'] == 'delay':
            add_event(i, step['str'], step['ori_pos'])
        else:
            pass

    # Maximum space for id
    max_id_space = max(len(str(id)) for id in ids) + 1

    # For each process, find the maximum space needed
    max_space = dict()
    for process in all_processes:
        max_space[process] = max(len(s) for s in events[process]) + 2

    print(max_space)

    # Now create the text file
    with open('sequence_diagram.txt', 'w', encoding='utf-8') as f:
        for i in range(num_events):
            # Print id
            f.write(' ' * (max_id_space - len(str(ids[i]))))
            f.write(str(ids[i]))
            for process in all_processes:
                text = events[process][i]
                text_len = len(events[process][i])
                space_remain = max_space[process] - text_len
                space_before = space_remain // 2
                space_after = (space_remain + 1) // 2
                f.write(' ' * space_before + text + ' ' * space_after)
            f.write('\n')
