from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst
class DataStoreMemory:
	"""docstring for DataStoryMemoy"""
	def __init__(self, name,value,dataStore_name):
		super(DataStoreMemory, self).__init__()
		self.type ="DataStoreMemory"
		self.name = name
		self.value=value
		self.dataStore_name=dataStore_name
		self.st = -1
		self.src_lines = [[]]
		self.dest_lines = [None]
	def __str__(self):
		return "name=%s,value=%s,dataStore_name=%s" %(self.name,str(self.value),self.dataStore_name)
	
	def get_hcsp(self):
		hp_body=list()
		
		hp_body.append(hcsp.InputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)))
		hp_body.append(hcsp.OutputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)))
		return hcsp.Sequence(hcsp.Assign(AVar(self.dataStore_name), AConst(self.value)),hcsp.OutputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)),hcsp.Loop(hcsp.Sequence(*hp_body)))

class DataStoreRead:
	"""docstring for DataStoreRead"""
	def __init__(self, name,dataStoreName):
		super(DataStoreRead, self).__init__()
		self.type="DataStoreRead"
		self.name = name
		self.dataStoreName=dataStoreName
		self.data_length=0
		self.st = -1
		self.src_lines = [[]]
		self.dest_lines = [None]
	def __str__(self):
		return "name=%s,dataStore_name=%s" %(self.name,str(self.value),self.dataStoreName)
	def get_hcsp(self,j):
		hp_body=list()
		for i in range(0,j):
			var="value"+str(i+1)
			hp_body.append(hcsp.InputChannel("ch_"+self.dataStore_name+"_"+var, AVar(var)))
		return hcsp.Sequence(hcsp.Loop(hcsp.Sequence(*hp_body)))
		