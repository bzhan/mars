"""Messages in Stateflow."""

class SF_Message:
	"""docstring for SF_Message"""
	def __init__(self, name="",data="",scope=None):
		self.name = name
		self.data=data
		self.scope=scope
	def __str__(self):
            return "{ name:%s ; data:%s ; scope:%s}" % (self.name, self.data,self.scope)

class SF_Data:
	"""docstring for SF_Data"""
	def __init__(self, name,value,scope):
		super(SF_Data, self).__init__()
		self.name = name
		self.value=value
		self.scope=scope
	def __str__(self):
            return "{ name:%s ; data:%s ; scope:%s}" % (self.name, self.value,self.scope)
		
		