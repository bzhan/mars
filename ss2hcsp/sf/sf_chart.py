from ss2hcsp.sf.sf_state import AND_State


class SF_Chart:
    def __init__(self, name, state):
        self.name = name
        self.state = state

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.state))
