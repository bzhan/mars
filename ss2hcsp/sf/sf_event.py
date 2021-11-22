"""Events in Stateflow."""

class SF_Event:
	def __init__(self, name="", trigger=None, scope=None, port=None):
		self.name = name
		self.trigger = trigger
		self.scope = scope
		self.port = port

	def __str__(self):
		return "{ name:%s ; trigger:%s ; scope:%s,port:%s}" % \
			(self.name, self.trigger,self.scope,self.port)
