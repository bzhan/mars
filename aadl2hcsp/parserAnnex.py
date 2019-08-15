"""Parse an AADL model with Behaviour Annex
"""
from ss2hcsp.hcsp.expr import *
from ss2hcsp.hcsp.hcsp import *
import re
import json
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


    def createHCSP(self, codelist):
        if not isinstance(codelist,list):
            return
        code = ' '.join(codelist)[:-1]
        var, state, trans = self._createParser(code)
        hcsp=''
        for s in state.keys():
            if 'INITIAL' in state[s]:
                now_state=s
                next_state=trans[s]['distination']
                hcsp += trans[s]['content']
                break

        while 'FINAL' not in state[now_state]:
            now_state = next_state
            next_state = trans[s]['distination']
            hcsp += trans[s]['content']

        return hcsp



    def _createParser(self, code):
        var=[]
        state={}
        trans={}

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
            if isinstance(p[1], HCSP) and isinstance(p[3],HCSP):
                p[0] = Sequence(*[p[1], p[3]])
            elif isinstance(p[1], HCSP):
                p[0] = p[1]
            elif isinstance(p[3], HCSP):
                p[0] = p[3]
            else:
                p[0] = ''


        def p_statement_assign(p):
            'statement : NAME ATTACHED expression '
            p[0]=Assign(str(p[1]),p[3])

        def p_statement_expr(p):
            """statement : expression  """
            p[0]=HCSP(p[1])

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
            if p[2] == '+':
                p[0] = PlusExpr(['+', '+'], [p[1], p[3]])
            elif p[2] == '-':
                p[0] = PlusExpr(['+', '-'], [p[1], p[3]])
            elif p[2] == '*':
                p[0] = TimesExpr(['*', '*'], [p[1], p[3]])
            elif p[2] == '\\':
                p[0] = TimesExpr(['*', '\\'], [p[1], p[3]])
            elif p[2]=='%':
                p[0] = TimesExpr(['*', '%'], [p[1], p[3]])
            elif p[2]=='=':
                p[0] = RelExpr('=', p[1], p[3])
            elif p[2] == '>':
                p[0] = RelExpr('>', p[1], p[3])
            elif p[2] == '<':
                p[0] = RelExpr('<', p[1], p[3])
            elif p[2]=='==':
                p[0] = RelExpr('==', p[1], p[3])
            elif p[2] == '!=':
                p[0] = RelExpr('!=', p[1], p[3])
            elif p[2]=='>=':
                p[0] = RelExpr('>=', p[1], p[3])
            elif p[2]=='<=':
                p[0] = RelExpr('<=', p[1], p[3])


        def p_expression_uminus(p):
            """statement : expression '!' """
            p[0] = Assign(str(p[1]), NegExpr(p[1]))

        def p_expression_group(p):
            "expression : '(' expression ')'"
            p[0] = p[2]

        def p_expression_number(p):
            "expression : NUMBER"
            p[0] = AConst(float(p[1]))
        def p_expression_name(p):
            "expression : NAME"
            p[0] = AVar(p[1])

        def p_expression_namelist(p):
            "expression : expression ',' expression"
            p[0]=[]
            if isinstance(p[1],AVar):
                p[0].append(str(p[1]))
            elif isinstance(p[1],list):
                p[0].append(v for v in p[1])

            if isinstance(p[3],AVar):
                p[0].append(str(p[3]))
            elif isinstance(p[3],list):
                p[0].append(v for v in p[3])

        def p_type_data(p):
            """type : INT
                   | FLOAT
                   | BOOLEAN """
        def p_define_variable(p):
            """statement : VARIABLES expression ':' type
                          | VARIABLES expression
                       """
            if isinstance(p[2],AVar):
                var.append(str(p[2]))
            elif isinstance(p[2],list):
                for v in p[2]:
                    var.append(v)

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
            state[p[2]]=p[4]

        def p_define_transtion(p):
            """statement : TRANSITIONS NAME ':' NAME LEFT_DIS ON DISPATCH RIGHT_DIS NAME LEFT_CURLY_BRA statement RIGHT_CURLY_BRA """
            trans[p[4]]={'distination':p[9],'content':str(p[11])}

        def p_if_statement(p):
            """ statement : IF '(' expression ')' statement  END IF  """
            p[0] = Condition(p[3], p[5])

        def p_while_statement(p):
            """ statement :  WHILE '(' expression ')' statement  END WHILE """
            p[0] = Loop(Condition(p[3], p[5]))

        def p_error(p):
            if p:
                print("Syntax error at '%s'" % p.value)
            else:
                print("Syntax error at EOF")

        yacc.yacc()
        yacc.parse(code)

        return var, state, trans


if __name__=='__main__':
    file='air_conditioner/air_conditioner.aadl'
    AP=AnnexParser()
    Annexs=AP.getAnnex(file)
    HP={}
    for th in Annexs.keys():
        HP[th]=AP.createHCSP(Annexs[th][1:-1])
    print(HP)






