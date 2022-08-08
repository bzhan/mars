from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
import gevent
from collections import OrderedDict
import sys
import traceback
import re
from os import listdir
from os.path import isfile, join, dirname
from multiprocessing import Process, Queue
from queue import Empty
import signal
import sys



from operator import pos

from ss2hcsp.hcsp import expr, hcsp
from ss2hcsp.hcsp.parser import parse_hoare_triple_with_meta, parse_expr_with_meta
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.hhlpy_without_dG import CmdVerifier
from hhlpy.wolframengine_wrapper import wl_prove
from hhlpy.z3wrapper import z3_prove
from hhlpy.wolframengine_wrapper import session, found_wolfram


import json

def runCompute(code):
    """Compute the verification condition information by the code received from the client editor.
    Return an array of verification condition information."""
    hoare_triple = parse_hoare_triple_with_meta(code)

    # Initialize the verifier
    verifier = CmdVerifier(
        pre=expr.list_conj(*hoare_triple.pre), 
        hp=hoare_triple.hp,
        post=hoare_triple.post,
        functions=hoare_triple.functions)

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

            assume = split_imp(vc.expr)[:-1]
            show = split_imp(vc.expr)[-1]

            label_computed = vc.comp_label
            method_stored = None
            
            pms_start_pos = -1
            pms_end_pos = -1
            

            # Case when the bottom most assertion of vc is a post condition.
            if vc.pc and vc.annot_pos is not None:
                assertion = hoare_triple.post[vc.annot_pos]

            # Case when the bottom most assertion of vc is a loop or an ode invariant.
            elif isinstance(hp, (hcsp.Loop, hcsp.ODE)) and vc.annot_pos is not None:
                assert hp.inv is not None
                assertion = hp.inv[vc.annot_pos]

            else:
                raise NotImplementedError
                
            proof_methods = assertion.proof_methods
            pms_meta = proof_methods.meta
            if pms_meta.empty:
                pms_meta.start_pos = assertion.meta.end_pos
                pms_meta.end_pos = assertion.meta.end_pos
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
                "assume": [str(asm) for asm in assume],
                "show": str(show),
                "label": str(vc.comp_label),
                "method": method_stored,
                "origin": origin,
                "pms_start_pos": pms_start_pos,
                "pms_end_pos": pms_end_pos
            })
    
    return vc_infos

def runVerify(formula, code, solver):
    formulaExpr = parse_expr_with_meta(formula)
    hoare_triple = parse_hoare_triple_with_meta(code)

    if solver == "z3":
        return z3_prove(formulaExpr, functions=hoare_triple.functions)
    elif solver == "wolfram":
        return wl_prove(formulaExpr)
    else:
        raise NotImplementedError

# This function runs `runCompute` and `runVerify` on a separate process
# ensuring that the main process is still available to receive client requests
def runComputationProcess(inputQueue, outputQueue):
    if found_wolfram:
        print("Starting Wolfram Engine", flush=True)
        session.start_future()
        print("Started Wolfram Engine", flush=True)
        def handler(signum, frame):
            print("Stopping Wolfram Engine", flush=True)
            session.terminate()
            print("Process ended.", flush=True)
            sys.exit()
        signal.signal(signal.SIGTERM, handler)
    else:
        print("Wolfram Engine not found", flush=True)
    
    outputQueue.put({"type": "computation_process_ready"})

    while True:
        msg = inputQueue.get() # Wait for next verification task

        if msg["type"] == "compute":
            try:
                vcs = runCompute(code=msg["code"])
                outputQueue.put({"vcs": vcs, "type": "computed"})
            except Exception as e:
                outputQueue.put({"error": str(e), "type": "computed"})

        elif msg["type"] == "verify":
            result = runVerify(
                formula=msg["formula"],
                code=msg["code"],
                solver=msg["solver"])
        
            outputQueue.put({
                "index": msg["index"], 
                "formula": msg["formula"], 
                "result": result, 
                "type": "verified"})

# These queues are used to communicate between the two processes
computationInputQueue = Queue()
computationOutputQueue = Queue()

def natural_sort(l): 
    convert = lambda text: int(text) if text.isdigit() else text.lower() 
    alphanum_key = lambda key: [convert(c) for c in re.split('([0-9]+)', key)] 
    return sorted(l, key=alphanum_key)

def getExampleList():
    path = join(dirname(__file__), "..", "examples")
    filenames = [f for f in listdir(path) if isfile(join(path, f))]
    filenames = natural_sort(filenames)
    return filenames

def getFileList(path):
    path = join(dirname(__file__), "..", "examples", path)
    filenames = [f for f in listdir(path) if isfile(join(path, f))]
    dirnames = [f for f in listdir(path) if not isfile(join(path, f))]
    filenames = natural_sort(filenames)
    dirnames = natural_sort(dirnames)
    return (dirnames, filenames)

def getExampleCode(example):
    file = join(dirname(__file__), "../examples", example)
    file = open(file,mode='r', encoding='utf-8')
    code = file.read()
    file.close()
    return code

def split_imp(e):
    """Split an implication expression into a list of its sub-expressions in order.
    Example, p -> q -> u into [p, q, u]"""
    if isinstance(e, expr.LogicExpr) and e.op == '->':
        return split_imp(e.exprs[0]) + split_imp(e.exprs[1])
    else:
        return [e]

computationProcess = None

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")
        global ws # TODO: Is there a better way than using global here?
        ws = self.ws

    def on_message(self, message):
        try:
            if message != None:
                msg = json.loads(message)
                print(msg, flush=True)
                # If the type of message received is "compute", 
                # the message has a code field, which is the document in editor,
                # then call runCompute function.
                if msg["type"] == "compute":
                    computationInputQueue.put(msg)

                # If the type of message received is "verify",
                # the message has the index, the formula and solver of corresponding vc.
                elif msg["type"] == "verify":
                    computationInputQueue.put(msg)

                elif msg["type"] == "get_example_list":
                    examples = getExampleList()
                    result = {"examples": examples, "type": "example_list"}
                    self.ws.send(json.dumps(result)) 
                
                elif msg["type"] == "get_file_list":
                    (dirs, files) = getFileList(msg["path"])
                    result = {"dirs": dirs, "files": files, "path": msg["path"], "type": "file_list"}
                    self.ws.send(json.dumps(result)) 

                elif msg["type"] == "load_file":
                    code = getExampleCode(msg["example"])
                    result = {"code": code, "type": "load_file"}
                    self.ws.send(json.dumps(result)) 

                elif msg["type"] == "cancel_computation":
                    global computationProcess
                    computationProcess.terminate()
                    computationProcess.join()
                    computationProcess = startComputationProcess()

                else:
                    raise NotImplementedError    
        except Exception as e:
            print(str(e), file=sys.stderr)
            print(traceback.format_exc(), file=sys.stderr)
            result_dict = {"error": str(e), "type": "error"}  
            self.ws.send(json.dumps(result_dict)) 

    def on_close(self, reason):
        print(reason)

    def on_error(self, ):
        print("Server Error")

def checkComputationProcess():
    try:
        result = computationOutputQueue.get(False)
        print("out!", flush=True)
        ws.send(json.dumps(result))
    except Empty:
        pass

def startComputationProcess():
    computationProcess = Process(daemon=True, target=runComputationProcess, 
            kwargs={"inputQueue": computationInputQueue, "outputQueue": computationOutputQueue})
    computationProcess.start()
    return computationProcess

if __name__ == "__main__":
    port = 8000
    server = WebSocketServer(
        ('', port),
        Resource(OrderedDict([('/', HHLPyApplication)]))
    )
    try:
        computationProcess = startComputationProcess()
        print("Running python websocket server on ws://localhost:{0}".format(port), flush=True)
        server.start()
        while True:
            checkComputationProcess() # Check whether there are new computation results
            gevent.sleep(0) # Pause to allow the server to handle new requests from the client
    except KeyboardInterrupt:
        print("KeyboardInterrupt")
        print("Closing python websocket server")
        server.stop()
