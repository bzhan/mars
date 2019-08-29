import tempfile
from xml.dom.minidom import parse as XMLparse
import codecs
import json


def get_attribute_value(block, attribute):
    attribute_names = []
    for node in block.getElementsByTagName(attribute):
        if node.getAttribute("Name"):
            attribute_names.append(node.getAttribute("Name"))
    return attribute_names


def portPickforSimulink(simulink_string):
    # have to use the temp file as a work around because the XMLparse only accepts the file as the input
    with tempfile.NamedTemporaryFile("w+") as in_f:
        in_f.write(simulink_string)
        in_f.flush()
        in_f.seek(0)
        parse_model = XMLparse(in_f)
        print("load model successfully")

    out_file = dict()
    simulink_models = parse_model.getElementsByTagName(name="Model")
    for model in simulink_models:
        model_name = model.getAttribute('Name')
    out_file["model_name"] = model_name
    # out_file.append(["model_name", model_name])

    interfaces = parse_model.getElementsByTagName(name="GraphicalInterface")
    for interface in interfaces:
        inports = get_attribute_value(block=interface, attribute="Inport")
        inport_names = []
        for inport in inports:
            inport_names.append(inport)
        out_file["Inport"] = inport_names
        # out_file.append(["Inport", inport])
        outports = get_attribute_value(block=interface, attribute="Outport")
        outport_names = []
        for outport in outports:
            outport_names.append(outport)
        out_file["Outport"] = outport_names
        # out_file.append(["Outport", outport])
    return out_file

if __name__ == '__main__':
    with open("simulink_isollete.xml") as f:
        data = f.read()
        print(portPickforSimulink(data))
