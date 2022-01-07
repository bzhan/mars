from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst
class Mux(SL_Block):
	"""docstring for Mux"""
	def __init__(self,name, inputs,displayOption,ports):
		super(Mux, self).__init__(name=name, num_dest=int(inputs), num_src=1, st=-1, type="mux")
		# self.name=name
		# self.type = "mux"
		self.inputs=inputs
		self.displayOption=displayOption
		self.signal_names = list()
		self.time_axises = list()
		self.data_axises = list()
		# self.num_src = 1
		# self.num_dest = int(inputs)
		self.ports=ports
		self.src_lines = [[]]
		self.dest_lines = [None] * self.num_dest
		# self.st = -1
		self.is_continuous = (self.st == 0)
	def __str__(self):
		return "%s Mux[inputs = %s, displayOption = %s]" % (self.name,str(self.inputs),str(self.displayOption))
	def __repr__(self):
		return str(self)

	def get_map(self):
		out_var = self.src_lines[0][0].name
		in_vars = [line.name for line in self.dest_lines]
		return [out_var, in_vars]

	def get_hp(self):
		hp=list()
		self.ports.sort()
		for port in self.ports:
			hp.append(hcsp.InputChannel(self.dest_lines[port-1].ch_name, AVar("out_tri"+str(port))))
			hp.append(hcsp.OutputChannel('ch_' + 'trig'+str(port), AVar('out_tri'+str(port))))
		
	
		return hcsp.Loop(hcsp.Sequence(*hp))
    
