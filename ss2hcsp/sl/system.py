import operator


class System:
    """Represents the HCSP system of a Simulink diagram"""
    def __init__(self, name="P"):
        self.type = "system"
        self.name = name
        self.discrete_processes = []
        self.continuous_processes = []

    def __eq__(self, other):
        if len(self.discrete_processes) != len(other.discrete_process) or \
                len(self.discrete_processes) != len(other.discrete_process):
            return False
        # Check the discrete processes
        for process in self.discrete_processes:
            matched = False
            for other_process in other.discrete_process:
                if process == other_process:
                    matched = True
                    break
            if not matched:
                return False
        # Check the continuous processes
        for process in self.continuous_processes:
            matched = False
            for other_process in other.continuous_process:
                if process == other_process:
                    matched = True
                    break
            if not matched:
                return False
        return True

    def __str__(self):
        self.discrete_processes.sort(key=operator.attrgetter('name'))
        self.continuous_processes.sort(key=operator.attrgetter('name'))
        processes = self.discrete_processes + self.continuous_processes
        main_process = self.name + " ::= " + "||".join(process.name for process in processes) + "\n\n"
        sub_processes = ""
        for process in processes:
            sub_processes += process.name + " ::= " + str(process) + "\n"
        return main_process + sub_processes
