class Junction:
    def __init__(self, ssid, out_trans, name="", actatived=False):
        self.ssid = ssid
        self.out_trans = out_trans
        self.name = name
        self.actatived = actatived

    def __str__(self):
        result = "JUN(" + self.ssid + ") activated=" + str(self.actatived) + "\n"
        for tran in self.out_trans:
            result += str(tran) + "State or Junction(" + tran.dst + ")\n"
        return result

    def activate(self):
        assert not self.actatived
        self.actatived = True

    def exit(self):
        assert self.actatived
        self.actatived = False

    def execute(self, event):
        pass
