"""Parse an AADL model with Behaviour Annex
"""
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr
from ss2hcsp.hcsp.hcsp import *
import re
import ply.lex as lex
import ply.yacc as yacc
import warnings
warnings.filterwarnings("ignore")

class AnnexParser(object):
    def __init__(self):
        self.Annexs={}
        self.HCSP=""

    def getAnnex(self, doc):
        with open(doc, 'r') as f:
            data = f.readlines()
        flag=0
        i=0
        while i<len(data):
            line=data[i].strip()
            if 'THREAD' in line.split() and 'IMPLEMENTATION' in line.split() and flag==0:
                thread_name=line.split()[-1].split('.')[0]
                flag=1
            if 'Annex' in line.split() or '{**' in line.split() and flag==1:
                annex_cont = []
                flag=2
            if flag==2:
                annex_cont.append(line)
            if '**};' in line.split() and flag==2:
                self.Annexs[thread_name] = annex_cont
                flag=0
            if 'END' in line.split() :
                flag=0
            i+=1
        return self.Annexs

    def createHCSP(self, code):
        self.var=[]
        self.state={}
        self.trans={}

        reserved = {
            'TRANSITIONS': 'TRANSITIONS',
            'STATES': 'STATES',
            'VARIABLES': 'VARIABLES',
            'INITIAL':'INITIAL',
            'COMPLETE':'COMPLETE',
            'FINAL': 'FINAL',
            'STATE': 'STATE',
            'int':'INT',
            'float': 'FLOAT',
            'boolean': 'BOOLEAN',
            'DISPATCH':'DISPATCH',
            'ON':'ON',
            'if':'IF',
            'while': 'WHILE',
            'end': 'END'
        }
        tokens = ['NAME',
                  'NUMBER',
                  'ATTACHED',
                  'RIGHT_CURLY_BRA',
                  'LEFT_CURLY_BRA',
                  'COMP_OP',
                  'LEFT_ANGLE_BRA',
                  'RIGHT_ANGLE_BRA',
                  'EQUALS',
                  'PLUS',
                  'MINUS',
                  'TIMES',
                  'DIVIDE',
                  'REMAINDER',
                  'LEFT_DIS',
                  'RIGHT_DIS'
        ]
        tokens = tokens + list(reserved.values())
        literals = [ '(',')',',',':',';','!']
        # Tokens
        t_EQUALS = r'='
        t_PLUS = r'\+'
        t_MINUS = r'-'
        t_TIMES = r'\*'
        t_DIVIDE = r'/'
        t_REMAINDER = r'%'
        t_ATTACHED=r':='
        t_LEFT_CURLY_BRA=r'\{'
        t_RIGHT_CURLY_BRA = r'\}'
        t_LEFT_ANGLE_BRA = r'<'
        t_RIGHT_ANGLE_BRA = r'>'
        t_NUMBER = r'\d+'
        t_LEFT_DIS=r'-\['
        t_RIGHT_DIS=r']->'

        def t_COMP_OP(t):
            r'==|>=|<=|<>'
            return t

        def t_NAME(t):
            r'[_A-Za-z]([_0-9A-Za-z]|::)*'
            t.type = reserved.get(t.value, 'NAME')  # Check for reserved words
            return t

        t_ignore = " \t"
        def t_newline(t):
            r'\n+'
            t.lexer.lineno += t.value.count("\n")

        def t_error(t):
            print("Illegal character '%s'" % t.value[0])
            t.lexer.skip(1)
        # Build the lexer
        lex.lex()
        # Parsing rules
        def p_statement_list(p):
            """ statement : statement ';' statement  """
            p[0]=str(p[1])+str(p[3])

        def p_statement_assign(p):
            'statement : NAME ATTACHED expression '
            p[0]=[str(p[1])+str(p[2])+str(p[3])]

        def p_statement_expr(p):
            """statement : expression  """
            p[0]=[str(p[1])]

        def p_expression_binop(p):
            '''expression : expression PLUS expression
                          | expression MINUS expression
                          | expression  TIMES expression
                          | expression DIVIDE expression
                          | expression REMAINDER expression
                          | expression EQUALS expression
                          | expression LEFT_ANGLE_BRA expression
                          | expression RIGHT_ANGLE_BRA expression
                          | expression COMP_OP expression '''
            p[0]=str(p[1])+str(p[2])+str(p[3])

        def p_expression_uminus(p):
            """expression : '-' expression
                         | expression '!' """
            p[0] = str(p[1])+str(p[2])

        def p_expression_group(p):
            "expression : '(' expression ')'"
            p[0] = p[2]

        def p_expression_number(p):
            "expression : NUMBER"
            p[0] = str(p[1])
        def p_expression_name(p):
            "expression : NAME"
            p[0] = [p[1]]

        def p_expression_namelist(p):
            "expression : expression ',' expression"
            p[0] = p[1]+p[3]

        def p_type_data(p):
            """type : INT
                   | FLOAT
                   | BOOLEAN """
        def p_define_variable(p):
            """statement : VARIABLES expression ':' type
                          | VARIABLES expression
                       """
            print(p[2])
            self.var.append(p[2])

        def p_state_list(p):
            """ state : state state
                       | INITIAL
                       | COMPLETE
                       | FINAL"""
            if len(p)==3:
                p[0]=p[1]+p[2]
            else:
                p[0]=[p[1]]

        def p_define_state(p):
            """statement : STATES NAME ':' state STATE  """
            print(p[2])
            self.state[p[2]]=p[4]

        def p_define_transtion(p):
            """statement : TRANSITIONS NAME ':' NAME LEFT_DIS ON DISPATCH RIGHT_DIS NAME LEFT_CURLY_BRA statement RIGHT_CURLY_BRA """
            self.trans[p[4]]={'distination':p[9],'content':p[11]}

        def p_if_statement(p):
            """ statement : IF '(' expression ')' statement  END IF  """
            

        def p_while_statement(p):
            """ statement :  WHILE '(' expression ')' statement  END WHILE """

        def p_error(p):
            if p:
                print("Syntax error at '%s'" % p.value)
            else:
                print("Syntax error at EOF")

        yacc.yacc()
        yacc.parse(code)
        print(self.state)


if __name__=='__main__':
    file='air_conditioner/air_conditioner.aadl'
    AP=AnnexParser()
    Annexs=AP.getAnnex(file)
    HP={}
    for th in Annexs.keys():
        HP[th]=AP.createHCSP(' '.join(Annexs[th][1:-1]).strip()[:-1])
    #print(HP)






