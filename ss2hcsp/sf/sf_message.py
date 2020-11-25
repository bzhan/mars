class SF_Message:
	"""docstring for SF_Message"""
	def __init__(self, name="",data="",scope=None):
		self.name = name
		self.data=data
		self.scope=scope
	def __str__(self):
            return "{ name:%s ; data:%s ; scope:%s}" % (self.name, self.data,self.scope)
		