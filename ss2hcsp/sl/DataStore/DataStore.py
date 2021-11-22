"""Simulink blocks DataStoreMemory and DataStoreRead."""

from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst
from ss2hcsp.sl.sl_block import SL_Block


class DataStoreMemory:
	"""Simulink block DataStoreMemory."""
	def __init__(self, name, value, dataStoreName):
		super(DataStoreMemory, self).__init__()
		self.type = "DataStoreMemory"
		self.name = name
		self.value = value
		self.dataStoreName = dataStoreName
		self.st = -1
		self.src_lines = [[]]
		self.dest_lines = [None]

	def __str__(self):
		return "name=%s,value=%s,dataStoreName=%s" % (
			self.name, str(self.value), self.dataStoreName)

	def __repr__(self):
		return "DataStoreMemory(%s,%s,%s)" % (self.name, str(self.value), self.dataStoreName)
	
	def get_hcsp(self):
		# hcsp.SelectComm(((hcsp.InputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)),hcsp.Skip()),(hcsp.OutputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)),hcsp.Skip())))
		# return hcsp.Sequence(hcsp.Assign(AVar(self.dataStore_name), AConst(self.value)),hcsp.Loop(hcsp.SelectComm((hcsp.OutputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)),hcsp.Skip()),(hcsp.InputChannel("ch_"+self.dataStore_name, AVar(self.dataStore_name)),hcsp.Skip()))))
		hp_body = [
			hcsp.OutputChannel("ch_"+self.dataStoreName, AVar(self.dataStoreName)),
			hcsp.InputChannel("ch_"+self.dataStoreName, AVar(self.dataStoreName))
		]
		return hcsp.Sequence(
			hcsp.Assign(AVar(self.dataStoreName), AConst(self.value)),
			hcsp.OutputChannel("ch_"+self.dataStoreName, AVar(self.dataStoreName)),
			hcsp.InputChannel("ch_"+self.dataStoreName, AVar(self.dataStoreName)),
			hcsp.Loop(hcsp.Sequence(*hp_body))
		)


class DataStoreRead(SL_Block):
	"""Simulink block DataStoreRead."""
	def __init__(self, name, dataStoreName):
		super(DataStoreRead, self).__init__("DataStoreRead", name, 1, 1, -1)
		self.dataStoreName = dataStoreName
		self.data_length = 0

	def __str__(self):
		return "name=%s,dataStore_name=%s" % (self.name, self.dataStoreName)

	def __repr__(self):
		return "DataStoreRead(%s,%s)" % (self.name, self.dataStoreName)

	def get_hcsp(self, j):
		hp_body = []
		for i in range(j):
			var = "value" + str(i + 1)
			hp_body.append(hcsp.InputChannel("ch_"+self.dataStore_name+"_"+var, AVar(var)))
		return hcsp.Sequence(hcsp.Loop(hcsp.Sequence(*hp_body)))
