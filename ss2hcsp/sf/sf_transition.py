"""Transition in Stateflow diagrams"""

from ss2hcsp.matlab.function import TransitionLabel


class Transition:
    def __init__(self, ssid, label, order=0, src="", dst=""):
        assert isinstance(label, TransitionLabel)
        self.ssid = ssid
        self.label = label
        self.order = order
        self.src = src
        self.dst = dst

    def __str__(self):
        if self.label:
            return "(%s)--%s-->(%s)" % (self.src, self.label, self.dst)
        else:
            return "(%s)--->(%s)" % (self.src, self.dst)

    def __repr__(self):
        return "Transition(%s, %s, %s, %s, %s)" % \
               (self.ssid, self.label, self.order, self.src, self.dst)
