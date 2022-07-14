from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
from collections import OrderedDict
import sys
import re
from os import listdir
from os.path import isfile, join, dirname

from operator import pos

from ss2hcsp.hcsp import expr, hcsp
from ss2hcsp.hcsp.parser import parse_hoare_triple_with_meta, parse_expr_with_meta
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.hhlpy2 import CmdVerifier
from hhlpy.wolframengine_wrapper import wl_prove
from hhlpy.z3wrapper import z3_prove
from hhlpy.wolframengine_wrapper import session, found_wolfram


import json


def runCompute(code, constants=set()):
    """Compute the verification condition information by the code received from the client editor.
    Return an array of verification condition information."""
    hoare_triple = parse_hoare_triple_with_meta(code)

    # Initialize the verifier
    verifier = CmdVerifier(
        pre=expr.list_conj(*hoare_triple.pre), 
        hp=hoare_triple.hp,
        post=expr.list_conj(*hoare_triple.post), 
        constants=constants)

    # Compute wp and verify
    verifier.compute_wp()

    # Return verification condition informations
    vc_infos = []

    for pos, vcs in verifier.get_all_vcs().items():

        for vc in vcs:
            # Use the bottom-most position `vc.pos[0]` to attach the VC to
            hp = get_pos(hoare_triple.hp, vc.pos[0][0])
            meta = get_pos(hoare_triple.hp, vc.pos[0][0]).meta
            if meta.empty:
                # LARK can't determine position of empty elements
                meta.column = 0
                meta.start_pos = 0
                meta.end_line = 1
                meta.end_pos = 0
            
            # Map origin positions in syntax tree to positions on the character level
            origin = []
            for originPos in vc.pos:
                if originPos[0] != ():
                    originMeta = get_pos(hoare_triple.hp, originPos[0]).meta
                    if not originMeta.empty:
                        origin.append({"from": originMeta.start_pos, "to": originMeta.end_pos})

            label_computed = vc.comp_label
            method_stored = None
            
            pms_start_pos = -1
            pms_end_pos = -1
            # TODO: Cases when the bottom most predicate of vc is an ode invariant or post-condition.
            # If the bottom most predicate of vc is a loop invariant.
            if isinstance(hp, hcsp.Loop) and vc.annot_pos is not None:
                if hp.inv:
                    inv = hp.inv[vc.annot_pos]
                    
                    proof_methods = inv.proof_methods
                    pms_meta = proof_methods.meta
                    if pms_meta.empty:
                        pms_meta.start_pos = inv.meta.end_pos
                        pms_meta.end_pos = inv.meta.end_pos
                    pms_start_pos = proof_methods.meta.start_pos
                    pms_end_pos = proof_methods.meta.end_pos
                    # If the method of this vc is stored in proof_methods,
                    # send the method back to the client, which will be used as the default method.
                    for proof_method in proof_methods.pms:
                        if str(label_computed) == str(proof_method.label):
                            method_stored = proof_method.method

            vc_infos.append({
                "line": meta.end_line,
                "column": meta.column,
                "start_pos": meta.start_pos,
                "end_pos": meta.end_pos,
                "formula": str(vc.expr),
                "label": str(vc.comp_label),
                "method": method_stored,
                "origin": origin,
                "pms_start_pos": pms_start_pos,
                "pms_end_pos": pms_end_pos
            })
    
    return vc_infos

def runVerify(formula, solver):
    """Verify the given verification condition of the solver.
    Return True or False
    """
    formula = parse_expr_with_meta(formula)

    if solver == "z3":
        return z3_prove(formula)
    elif solver == "wolfram":
        return wl_prove(formula)
    else:
        raise NotImplementedError

def natural_sort(l): 
    convert = lambda text: int(text) if text.isdigit() else text.lower() 
    alphanum_key = lambda key: [convert(c) for c in re.split('([0-9]+)', key)] 
    return sorted(l, key=alphanum_key)

def getExampleList():
    path = join(dirname(__file__), "..", "examples")
    filenames = [f for f in listdir(path) if isfile(join(path, f))]
    filenames = natural_sort(filenames)
    return filenames

def getExampleCode(example):
    file = join(dirname(__file__), "../examples", example)
    file = open(file,mode='r')
    code = file.read()
    file.close()
    return code

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")


    def on_message(self, message):
        try:
            if message != None:
                msg = json.loads(message)
                print(msg, flush=True)
                # If the type of message received is "compute", 
                # the message has a code field, which is the document in editor,
                # then call runCompute function.
                if msg["type"] == "compute":
                    vcs = runCompute(code=msg["code"])
                    vcs_dict = {"vcs": vcs, "type": "computed"}
                    self.ws.send(json.dumps(vcs_dict))

                # If the type of message received is "verify",
                # the message has the index, the formula and solver of corresponding vc.
                elif msg["type"] == "verify":
                    result = runVerify(formula=msg["formula"], solver=msg["solver"])
                    index_vc_result = {"index":msg["index"], 
                                       "formula": msg["formula"], 
                                       "result": result, 
                                       "type": "verified"}
                    self.ws.send(json.dumps(index_vc_result))

                elif msg["type"] == "get_example_list":
                    examples = getExampleList()
                    result = {"examples": examples, "type": "example_list"}
                    self.ws.send(json.dumps(result)) 

                elif msg["type"] == "load_example":
                    code = getExampleCode(msg["example"])
                    result = {"code": code, "type": "load_example"}
                    self.ws.send(json.dumps(result)) 

                else:
                    raise NotImplementedError    
        except Exception as e:
            print(str(e), file=sys.stderr)
            result_dict = {"error": str(e), "type": "error"}  
            self.ws.send(json.dumps(result_dict)) 

    def on_close(self, reason):
        print(reason)

    def on_error(self, ):
        print("Server Error")

if __name__ == "__main__":
    port = 8000
    server = WebSocketServer(
        ('', port),
        Resource(OrderedDict([('/', HHLPyApplication)]))
    )
    try:
        if found_wolfram:
            print("Starting Wolfram Engine")
            session.start()
        else:
            print("Wolfram Engine not found")
        print("Running python websocket server on ws://localhost:{0}".format(port), flush=True)
        server.serve_forever()
    except KeyboardInterrupt:
        print("KeyboardInterrupt")
        print("Closing python websocket server")
        server.close()
        if found_wolfram:
            print("Terminating Wolfram Engine")
            session.terminate()
