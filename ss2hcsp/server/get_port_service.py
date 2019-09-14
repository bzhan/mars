import random
from ss2hcsp.server.portParser.aadlModel.portParseAADL import aadl_parser
from ss2hcsp.server.portParser.simulinkModel.portParseSimulink import portPickforSimulink

def get_port_service(simulink_code):
    name = str(random.randint(0, 10))
    return {
        "name": name,
        "in_port": [
            {"name": "port1", "type": "int"},
            {"name": "port2", "type": "string"}
        ],
        "out_port": [{"name": "port3", "type": "int"}]
    }

def get_simulink_port_service(simulink_code):
    return portPickforSimulink(simulink_code)

def get_aadl_port_service(aadl_code):
    return aadl_parser(aadl_code)
