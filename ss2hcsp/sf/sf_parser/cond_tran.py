class Expr:
    """Base class for matlab expressions."""
    def __init__(self):
        pass

    def get_vars(self):
        """Returns set of variables in the expression."""
        raise NotImplementedError

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class CondTran:
	def __init__(self, event, cond, cond_act, tran_act):
		self.event = event
		self.cond = cond
		self.cond_act = cond_act
		self.tran_act = tran_act
	
	def __str__(self):
		return "%s[%s]{%s}/{%s}" % (self.event,self.cond,self.cond_act,self.tran_act)

	def __repr__(self):
		return "CondTrans(%s, %s, %s, %s)" % (self.event,self.cond,self.cond_act,self.tran_act)



class CondExpr:
	def __init__(self, op, expr1, expr2):
		self.op = op
		self.expr1 = expr1
		self.expr2 = expr2
	def __repr__(self):
		return "Rel(%s, %s, %s)" % (self.op, repr(self.expr1), repr(self.expr2))

	def __str__(self):
		return str(self.expr1) + " " + self.op + " " + str(self.expr2)

	def __eq__(self, other):
		return isinstance(other, RelExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

	def __hash__(self):
		return hash(("Rel", self.op, self.expr1, self.expr2))

	def neg(self):
		return RelExpr(RelExpr.neg_table[self.op], self.expr1, self.expr2)

	def get_vars(self):
		return self.expr1.get_vars().union(self.expr2.get_vars())

	def subst(self, inst):
		return RelExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))
class DirectName:
	"""docstring for ClassName"""
	def __init__(self, expr):
		self.exprs = expr

	def __str__(self):
		return str(".".join(str(arg) for arg in self.exprs))

	def __repr__(self):
		return "DirectName(%s)" %(".".join(repr(arg) for arg in self.exprs))
		

		