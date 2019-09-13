
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = "NAME NUMBER ATTACHED RIGHT_CURLY_BRA LEFT_CURLY_BRA COMP_OP LEFT_ANGLE_BRA RIGHT_ANGLE_BRA EQUALS PLUS MINUS TIMES DIVIDE REMAINDER LEFT_DIS RIGHT_DIS TRANSITIONS STATES VARIABLES INITIAL COMPLETE FINAL STATE INT FLOAT BOOLEAN DISPATCH ON IF WHILE END statement : statement ';' statement  statement : NAME ATTACHED expression statement : expression  expression : expression PLUS expression\n                          | expression MINUS expression\n                          | expression  TIMES expression\n                          | expression DIVIDE expression\n                          | expression REMAINDER expression\n                          | expression EQUALS expression\n                          | expression LEFT_ANGLE_BRA expression\n                          | expression RIGHT_ANGLE_BRA expression\n                          | expression COMP_OP expression statement : expression '!' expression : '(' expression ')'expression : NUMBERexpression : NAMEexpression : expression ',' expressiontype : INT\n                   | FLOAT\n                   | BOOLEAN statement : VARIABLES expression ':' type\n                          | VARIABLES expression\n                        state : state state\n                       | INITIAL\n                       | COMPLETE\n                       | FINALstatement : STATES NAME ':' state STATE  statement : TRANSITIONS NAME ':' NAME LEFT_DIS ON DISPATCH RIGHT_DIS NAME LEFT_CURLY_BRA statement RIGHT_CURLY_BRA  statement : IF '(' expression ')' statement  END IF   statement :  WHILE '(' expression ')' statement  END WHILE "
    
_lr_action_items = {'NAME':([0,4,5,6,8,11,12,14,15,16,17,18,19,20,21,22,23,28,30,45,58,59,71,73,],[2,25,26,27,25,2,25,25,25,25,25,25,25,25,25,25,25,25,25,57,2,2,72,2,]),'VARIABLES':([0,11,58,59,73,],[4,4,4,4,4,]),'STATES':([0,11,58,59,73,],[5,5,5,5,5,]),'TRANSITIONS':([0,11,58,59,73,],[6,6,6,6,6,]),'IF':([0,11,58,59,66,73,],[7,7,7,7,69,7,]),'WHILE':([0,11,58,59,67,73,],[9,9,9,9,70,9,]),'(':([0,4,7,8,9,11,12,14,15,16,17,18,19,20,21,22,23,28,30,58,59,73,],[8,8,28,8,30,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,]),'NUMBER':([0,4,8,11,12,14,15,16,17,18,19,20,21,22,23,28,30,58,59,73,],[10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,]),'$end':([1,2,3,10,13,24,25,31,32,33,34,35,36,37,38,39,40,41,42,47,49,50,51,52,61,69,70,75,],[0,-16,-3,-15,-13,-22,-16,-1,-2,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,-21,-18,-19,-20,-27,-29,-30,-28,]),';':([1,2,3,10,13,24,25,31,32,33,34,35,36,37,38,39,40,41,42,47,49,50,51,52,61,63,64,69,70,74,75,],[11,-16,-3,-15,-13,-22,-16,11,-2,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,-21,-18,-19,-20,-27,11,11,-29,-30,11,-28,]),'ATTACHED':([2,],[12,]),'!':([2,3,10,25,33,34,35,36,37,38,39,40,41,42,47,],[-16,13,-15,-16,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,]),'PLUS':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,14,-15,14,-16,14,14,14,14,14,14,14,14,14,14,14,14,14,-14,14,]),'MINUS':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,15,-15,15,-16,15,15,15,15,15,15,15,15,15,15,15,15,15,-14,15,]),'TIMES':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,16,-15,16,-16,16,16,16,16,16,16,16,16,16,16,16,16,16,-14,16,]),'DIVIDE':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,17,-15,17,-16,17,17,17,17,17,17,17,17,17,17,17,17,17,-14,17,]),'REMAINDER':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,18,-15,18,-16,18,18,18,18,18,18,18,18,18,18,18,18,18,-14,18,]),'EQUALS':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,19,-15,19,-16,19,19,19,19,19,19,19,19,19,19,19,19,19,-14,19,]),'LEFT_ANGLE_BRA':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,20,-15,20,-16,20,20,20,20,20,20,20,20,20,20,20,20,20,-14,20,]),'RIGHT_ANGLE_BRA':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,21,-15,21,-16,21,21,21,21,21,21,21,21,21,21,21,21,21,-14,21,]),'COMP_OP':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,22,-15,22,-16,22,22,22,22,22,22,22,22,22,22,22,22,22,-14,22,]),',':([2,3,10,24,25,29,32,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-16,23,-15,23,-16,23,23,23,23,23,23,23,23,23,23,23,23,23,-14,23,]),'END':([2,3,10,13,24,25,31,32,33,34,35,36,37,38,39,40,41,42,47,49,50,51,52,61,63,64,69,70,75,],[-16,-3,-15,-13,-22,-16,-1,-2,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,-21,-18,-19,-20,-27,66,67,-29,-30,-28,]),'RIGHT_CURLY_BRA':([2,3,10,13,24,25,31,32,33,34,35,36,37,38,39,40,41,42,47,49,50,51,52,61,69,70,74,75,],[-16,-3,-15,-13,-22,-16,-1,-2,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,-21,-18,-19,-20,-27,-29,-30,75,-28,]),':':([10,24,25,26,27,33,34,35,36,37,38,39,40,41,42,47,],[-15,43,-16,44,45,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,-14,]),')':([10,25,29,33,34,35,36,37,38,39,40,41,42,46,47,48,],[-15,-16,47,-4,-5,-6,-7,-8,-9,-10,-11,-12,-17,58,-14,59,]),'INT':([43,],[50,]),'FLOAT':([43,],[51,]),'BOOLEAN':([43,],[52,]),'INITIAL':([44,53,54,55,56,60,],[54,54,-24,-25,-26,54,]),'COMPLETE':([44,53,54,55,56,60,],[55,55,-24,-25,-26,55,]),'FINAL':([44,53,54,55,56,60,],[56,56,-24,-25,-26,56,]),'STATE':([53,54,55,56,60,],[61,-24,-25,-26,-23,]),'LEFT_DIS':([57,],[62,]),'ON':([62,],[65,]),'DISPATCH':([65,],[68,]),'RIGHT_DIS':([68,],[71,]),'LEFT_CURLY_BRA':([72,],[73,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'statement':([0,11,58,59,73,],[1,31,63,64,74,]),'expression':([0,4,8,11,12,14,15,16,17,18,19,20,21,22,23,28,30,58,59,73,],[3,24,29,3,32,33,34,35,36,37,38,39,40,41,42,46,48,3,3,3,]),'type':([43,],[49,]),'state':([44,53,60,],[53,60,60,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> statement","S'",1,None,None,None),
  ('statement -> statement ; statement','statement',3,'p_statement_list','parserAnnex.py',145),
  ('statement -> NAME ATTACHED expression','statement',3,'p_statement_assign','parserAnnex.py',157),
  ('statement -> expression','statement',1,'p_statement_expr','parserAnnex.py',161),
  ('expression -> expression PLUS expression','expression',3,'p_expression_binop','parserAnnex.py',165),
  ('expression -> expression MINUS expression','expression',3,'p_expression_binop','parserAnnex.py',166),
  ('expression -> expression TIMES expression','expression',3,'p_expression_binop','parserAnnex.py',167),
  ('expression -> expression DIVIDE expression','expression',3,'p_expression_binop','parserAnnex.py',168),
  ('expression -> expression REMAINDER expression','expression',3,'p_expression_binop','parserAnnex.py',169),
  ('expression -> expression EQUALS expression','expression',3,'p_expression_binop','parserAnnex.py',170),
  ('expression -> expression LEFT_ANGLE_BRA expression','expression',3,'p_expression_binop','parserAnnex.py',171),
  ('expression -> expression RIGHT_ANGLE_BRA expression','expression',3,'p_expression_binop','parserAnnex.py',172),
  ('expression -> expression COMP_OP expression','expression',3,'p_expression_binop','parserAnnex.py',173),
  ('statement -> expression !','statement',2,'p_expression_uminus','parserAnnex.py',201),
  ('expression -> ( expression )','expression',3,'p_expression_group','parserAnnex.py',205),
  ('expression -> NUMBER','expression',1,'p_expression_number','parserAnnex.py',209),
  ('expression -> NAME','expression',1,'p_expression_name','parserAnnex.py',212),
  ('expression -> expression , expression','expression',3,'p_expression_namelist','parserAnnex.py',216),
  ('type -> INT','type',1,'p_type_data','parserAnnex.py',229),
  ('type -> FLOAT','type',1,'p_type_data','parserAnnex.py',230),
  ('type -> BOOLEAN','type',1,'p_type_data','parserAnnex.py',231),
  ('statement -> VARIABLES expression : type','statement',4,'p_define_variable','parserAnnex.py',233),
  ('statement -> VARIABLES expression','statement',2,'p_define_variable','parserAnnex.py',234),
  ('state -> state state','state',2,'p_state_list','parserAnnex.py',243),
  ('state -> INITIAL','state',1,'p_state_list','parserAnnex.py',244),
  ('state -> COMPLETE','state',1,'p_state_list','parserAnnex.py',245),
  ('state -> FINAL','state',1,'p_state_list','parserAnnex.py',246),
  ('statement -> STATES NAME : state STATE','statement',5,'p_define_state','parserAnnex.py',253),
  ('statement -> TRANSITIONS NAME : NAME LEFT_DIS ON DISPATCH RIGHT_DIS NAME LEFT_CURLY_BRA statement RIGHT_CURLY_BRA','statement',12,'p_define_transtion','parserAnnex.py',257),
  ('statement -> IF ( expression ) statement END IF','statement',7,'p_if_statement','parserAnnex.py',262),
  ('statement -> WHILE ( expression ) statement END WHILE','statement',7,'p_while_statement','parserAnnex.py',266),
]
