class SF_Event:
	def __init__(self, name="",trigger=None,scope=None):
		self.name = name
		self.trigger=trigger
		self.scope=scope
	def __str__(self):
            return "{ name:%s ; trigger:%s ; scope:%s}" % (self.name, self.trigger,self.scope)
