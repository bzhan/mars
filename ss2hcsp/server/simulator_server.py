from flask import Flask
from flask import request
import json

app = Flask(__name__)


@app.route('/')
def hello_world():
    return "Hello, World!"


@app.route('/process', methods=['POST'])
def process():
    data = json.loads(request.get_data(as_text=True))
    hcsp_code = data['code']
    hcsp_input = data['input']
    return hcsp_code + hcsp_input


if __name__ == '__main__':
    app.run(debug=True)
