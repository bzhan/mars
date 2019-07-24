import operator


class System:
    """Represents the HCSP system of a Simulink diagram"""
    def __init__(self, name="P"):
        self.type = "system"
        self.name = name
        self.discrete_processes = []
        self.continuous_processes = []

    def __eq__(self, other):
        if self.type != other.type or len(self.discrete_processes) != len(other.discrete_processes) or \
                len(self.continuous_processes) != len(other.continuous_processes):
            return False
        # Sort the discrete processes
        discrete_processes = sorted(self.discrete_processes, key=lambda x: str(x))
        other_processes = sorted(other.discrete_processes, key=lambda x: str(x))
        if discrete_processes != other_processes:
            return False
        # Sort the continuous processes
        continuous_processes = sorted(self.continuous_processes, key=lambda x: str(x))
        other_processes = sorted(other.continuous_processes, key=lambda x: str(x))
        if continuous_processes != other_processes:
            return False
        return True

    def __str__(self):
        self.discrete_processes.sort(key=operator.attrgetter('name'))
        self.continuous_processes.sort(key=operator.attrgetter('name'))
        processes = self.discrete_processes + self.continuous_processes
        main_process = self.name + " ::= " + "||".join(process.name for process in processes) + "\n"
        sub_processes = ""
        for process in processes:
            sub_processes += process.name + " ::= " + str(process) + "\n"
        return main_process + sub_processes
