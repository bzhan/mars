class Transition:
    def __init__(self, ssid, label, src="", dst=""):
        self.ssid = ssid
        self.label = label
        self.src = src
        self.dst = dst

    def __str__(self):
        return "Tran(%s)--%s-->" % (self.ssid, self.label)

    def __repr__(self):
        return "Transition(%s, %s, %s, %s)" % \
               (self.ssid, self.label, self.src, self.dst)

    def parse(self):
        pass
