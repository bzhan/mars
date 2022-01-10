from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
from collections import OrderedDict

from operator import pos

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import parse_aexpr_with_meta, parse_bexpr_with_meta, parse_hp_with_meta
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.hhlpy2 import CmdVerifier

import json


def runVerify(pre, hp, post, constants=set()):
    pre = parse_bexpr_with_meta(pre)

    hp = parse_hp_with_meta(hp)
    post = parse_bexpr_with_meta(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants)

    # Compute wp and verify
    verifier.compute_wp()

    # Return verification conditions
    verificationConditions = []
    for pos, vcs in verifier.get_all_vcs().items():
        meta = get_pos(hp, pos[0]).meta
        for vc in vcs:
            verificationConditions.append({
                "line": meta.line,
                "column": meta.column,
                "start_pos": meta.start_pos,
                "end_line": meta.end_line,
                "end_column": meta.end_column,
                "end_pos": meta.end_pos,
                "vc": str(vc)
            })

    return json.dumps(verificationConditions)

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")

    def on_message(self, message):
        if message != None:
            msg = json.loads(message)
            print(msg, flush=True)
            vcs = runVerify(msg["pre"], msg["hp"], msg["post"]);
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
