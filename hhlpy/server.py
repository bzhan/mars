from geventwebsocket import WebSocketServer, WebSocketApplication, Resource
from collections import OrderedDict

class HHLPyApplication(WebSocketApplication):
    def on_open(self):
        print("Connection opened")

    def on_message(self, message):
        self.ws.send(message)

    def on_close(self, reason):
        print(reason)

WebSocketServer(
    ('', 8000),
    Resource(OrderedDict([('/', HHLPyApplication)]))
).serve_forever()
