from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
from collections import OrderedDict

from operator import pos

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy2 import CmdVerifier

import json


def runVerify(pre, hp, post, constants=set()):
    pre = bexpr_parser.parse(pre)

    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants)

    # Compute wp and verify
    verifier.compute_wp()

    # Return verification conditions
    verificationConditions = {}
    for pos, vcs in verifier.get_all_vcs().items():
        verificationConditions[str(pos)] = []
        for vc in vcs:
            verificationConditions[str(pos)].append(str(vc))

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
