from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
from collections import OrderedDict

from operator import pos

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import parse_aexpr_with_meta, parse_bexpr_with_meta, parse_hp_with_meta
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.hhlpy2 import CmdVerifier

import json


def runVerify(pre, hp, post, z3, wolfram_engine, constants=set()):
    pre = parse_bexpr_with_meta(pre)

    hp = parse_hp_with_meta(hp)
    post = parse_bexpr_with_meta(post)

    z3 = parse_bexpr_with_meta(z3)
    wolfram_engine = parse_bexpr_with_meta(wolfram_engine)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants, 
                           z3=z3, wolfram_engine=wolfram_engine)

    # Compute wp and verify
    verifier.compute_wp()

    # Return verification conditions
    verificationConditions = []
    for pos, vcs in verifier.get_all_vcs().items():
        meta = get_pos(hp, pos[0]).meta
        for vc in vcs:
            vc_result = verifier.verify_vc(vc)
            verificationConditions.append({
                "line": meta.line,
                "column": meta.column,
                "start_pos": meta.start_pos,
                "end_line": meta.end_line,
                "end_column": meta.end_column,
                "end_pos": meta.end_pos,
                "vc": str(vc),
                "vc_result": vc_result
            })

    return json.dumps(verificationConditions)

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")

    def on_message(self, message):
        if message != None:
            msg = json.loads(message)
            print(msg, flush=True)
            vcs = runVerify(pre=msg["pre"], hp=msg["hp"], post=msg["post"], 
                            z3=msg["z3"], wolfram_engine=msg["wolfram_engine"])
            self.ws.send(vcs)

    def on_close(self, reason):
        print(reason)

if __name__ == "__main__":
    port = 8000
    print("Running python websocket server on ws://localhost:{0}".format(port), flush=True)
    WebSocketServer(
        ('', port),
        Resource(OrderedDict([('/', HHLPyApplication)]))
    ).serve_forever()
