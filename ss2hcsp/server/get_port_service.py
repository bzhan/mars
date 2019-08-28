import random
def get_port_service(simulink_code):
    name = str(random.randint(0, 10))
    return {"name": name, "in_port": [{"name": "port1", "type": "int"}, {"name": "port2", "type": "string"}],
            "out_port": [{"name": "port3", "type": "int"}]}
