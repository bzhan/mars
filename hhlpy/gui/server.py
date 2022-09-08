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
import webbrowser
from threading import Timer
from flask import Flask, send_from_directory, redirect


from operator import pos

from ss2hcsp.hcsp import expr, hcsp
from ss2hcsp.hcsp.parser import parse_hoare_triple_with_meta, parse_expr_with_meta
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.hhlpy import CmdVerifier
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
        pre=hoare_triple.pre, 
        hp=hoare_triple.hp,
        post=hoare_triple.post,
        functions=hoare_triple.functions)

    # Compute wp and verify
    verifier.compute_wp()

    # Return verification condition informations
    vc_infos = []

    for _, vcs in verifier.get_all_vcs().items():

        for vc in vcs:
            assume = split_imp(vc.expr)[:-1]
            show = split_imp(vc.expr)[-1] 


            # Get the proof method
            label_computed = vc.comp_label
            method_stored = None
            
            pms_start_pos = -1
            pms_end_pos = -1

            # Use the bottom-most assertion to attach the VC to
            assert vc.bottom_loc is not None
            bottom_loc = vc.bottom_loc
 
            # Case when the bottom-most assertion of vc is a post condition.
            if bottom_loc.isPost:
                bottom_ast = hoare_triple.post[vc.bottom_loc.index]

            # Case when the bottom-most assertion of vc is a loop or an ode invariant.
            elif bottom_loc.isInv:
                assert bottom_loc.hp_pos is not None
                hp = get_pos(hoare_triple.hp, vc.bottom_loc.hp_pos)

                assert isinstance(hp, (hcsp.Loop, hcsp.ODE))
                bottom_ast = hp.inv[vc.bottom_loc.index]
            
            else:
                raise NotImplementedError

            proof_methods = bottom_ast.proof_methods
            pms_meta = proof_methods.meta
            if pms_meta.empty:
                pms_meta.start_pos = bottom_ast.meta.end_pos
                pms_meta.end_pos = bottom_ast.meta.end_pos
            pms_start_pos = proof_methods.meta.start_pos
            pms_end_pos = proof_methods.meta.end_pos
            # If the method of this vc is stored in proof_methods,
            # send the method back to the client, which will be used as the default method.
            for proof_method in proof_methods.pms:
                if str(label_computed) == str(proof_method.label):
                    method_stored = proof_method.method


            # Map origin positions in syntax tree to positions on the character level
            originRanges = []
            # Append the hcsp program ranges.
            for originPos in vc.path:
                hp = get_pos(hoare_triple.hp, originPos[0])

                if isinstance(hp, hcsp.ODE):
                    from_pos = hp.meta.start_pos + 1
                    to_pos = hp.constraint.meta.end_pos
                else:
                    from_pos = hp.meta.start_pos
                    to_pos = hp.meta.end_pos
                
                originRanges.append({"from": from_pos, "to": to_pos})

            # Append the expression ranges.
            for origin in vc.origins:
                print("origin:", origin)
                if origin.isPre:
                    originMeta = hoare_triple.pre[origin.index].meta
                    to = originMeta.end_pos
               
                elif origin.isConstraint:
                    assert origin.hp_pos is not None
                    hp = get_pos(hoare_triple.hp, origin.hp_pos)
                    assert isinstance(hp, hcsp.ODE)
                    originMeta = hp.constraint.meta
                    to = originMeta.end_pos

                elif origin.isGhost:
                    assert origin.hp_pos is not None
                    hp = get_pos(hoare_triple.hp, origin.hp_pos)
                    assert isinstance(hp, hcsp.ODE)
                    originMeta = hp.ghosts[origin.index].meta
                    to = originMeta.end_pos

                elif origin.isInv or origin.isPost:
                    if origin.isInv:
                        assert origin.hp_pos is not None
                        hp = get_pos(hoare_triple.hp, origin.hp_pos)
                        assert isinstance(hp, (hcsp.Loop, hcsp.ODE))
                        assertion = hp.inv[origin.index]
                    else:
                        assertion = hoare_triple.post[origin.index]

                    originMeta = assertion.meta
                    proof_methods = assertion.proof_methods
                    pms_meta = proof_methods.meta
                    if pms_meta.empty:
                        pms_meta.start_pos = assertion.meta.end_pos
                        pms_meta.end_pos = assertion.meta.end_pos
                    
                    to = pms_meta.start_pos
                else:
                    raise NotImplementedError
                originRanges.append({"from": originMeta.start_pos, "to": to})


            vc_infos.append({
                "formula": str(vc.expr),
                "assume": [str(asm) for asm in assume],
                "show": str(show),
                "label": str(vc.comp_label),
                "method": method_stored,
                "origin": originRanges,
                "pms_start_pos": pms_start_pos,
                "pms_end_pos": pms_end_pos
            })
    
    return vc_infos

def runVerify(formula, code, solver):
    formulaExpr = parse_expr_with_meta(formula)
    hoare_triple = parse_hoare_triple_with_meta(code)

    if solver == "z3":
        return z3_prove(formulaExpr, functions=hoare_triple.functions)
    elif solver == "wolfram" and not found_wolfram:
        raise Exception("Wolfram Engine not found.")
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
                outputQueue.put({"vcs": vcs, "type": "computed", "file": msg["file"]})
            except Exception as e:
                traceback.print_exc()
                outputQueue.put({"error": str(e), "type": "computed", "file": msg["file"]})

        elif msg["type"] == "verify":
            try:
                result = runVerify(
                    formula=msg["formula"],
                    code=msg["code"],
                    solver=msg["solver"])
            except Exception as e:
                traceback.print_exc()
                outputQueue.put({"error": str(e), "type": "error", "file": msg["file"]})
        
            outputQueue.put({
                "file": msg["file"],
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

def getFileCode(example):
    file = join(dirname(__file__), "../examples", example)
    file = open(file, mode='r', encoding='utf-8')
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
ws = None

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")
        global ws # TODO: Is there a better way than using global here?
        ws = self.ws

    def on_message(self, message):
        try:
            if message != None:
                print(message, flush=True)
                msg = json.loads(message)
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
                    code = getFileCode(msg["file"])
                    result = {"file": msg["file"], "code": code, "type": "load_file"}
                    self.ws.send(json.dumps(result)) 

                elif msg["type"] == "cancel_computation":
                    global computationProcess
                    computationProcess.terminate()
                    computationProcess.join()
                    computationProcess = startComputationProcess()

                elif msg["type"] == "save_file":
                    file = join(dirname(__file__), "../examples", msg["file"])
                    file = open(file, mode='w', encoding='utf-8')
                    file.write(msg["code"])
                    file.close()

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
    if ws is not None:
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

def startHttpServer(port):
    print(dirname(__file__))
    app = Flask('hhlpy', root_path=dirname(__file__))

    @app.route('/')
    def index():
        return redirect('/index.html')

    @app.route('/<path:path>')
    def send_static(path):
        return send_from_directory('dist', path)

    app.run(port=port)

def startHttpProcess(port):
    httpProcess = Process(daemon=True, target=startHttpServer, args=[port])
    httpProcess.start()

def start(port, openBrowser, http):
    websocketServer = WebSocketServer(
        ('', port),
        Resource(OrderedDict([('/', HHLPyApplication)]))
    )
    try:
        computationProcess = startComputationProcess()
        if http:
            startHttpProcess(port)
        if openBrowser:
            def open_browser():
                webbrowser.open_new('http://127.0.0.1:{0}/'.format(port))
            Timer(3, open_browser).start();
        print("Running websocket server on ws://localhost:{0}".format(port), flush=True)
        websocketServer.start()
        while True:
            checkComputationProcess() # Check whether there are new computation results
            gevent.sleep(0) # Pause to allow the server to handle new requests from the client
    except KeyboardInterrupt:
        print("KeyboardInterrupt")
        print("Closing python websocket server")
        websocketServer.stop()

if __name__ == "__main__":
    start(8000, False, False)
