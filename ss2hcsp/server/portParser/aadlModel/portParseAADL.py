
from xml.dom.minidom import parse as XMLparse
import codecs
import json
import tempfile


def parse_aadlmodel(model):
    """Return instances of the model separated by type."""
    nodes = model.childNodes
    features = [node for node in nodes if node.nodeName == 'featureInstance']
    components = [node for node in nodes if node.nodeName == 'componentInstance']
    connections = [node for node in nodes if node.nodeName == 'connectionInstance']
    opas = [node for node in nodes if node.nodeName == 'ownedPropertyAssociation']

    return features, components, connections, opas

def getFeatures(features):
    """Interpret a list of features."""
    Feas = []
    for feature in features:
        fea = {}
        fea['name'] = feature.getAttribute('name')
        if feature.getAttribute('direction') != "":
            fea['direction'] = feature.getAttribute('direction')
        else:
            fea['direction'] = 'in'
        fea['type'] = feature.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Feas.append(fea)
    return Feas

def aadl_parser(aadl_string):
    """Parse the given XML file, add the read info into dic."""
    with tempfile.NamedTemporaryFile("w+") as in_f:
        in_f.write(aadl_string)
        in_f.flush()
        in_f.seek(0)
        parse_model = XMLparse(in_f)

    out_file = dict()
    model = parse_model.getElementsByTagName('instance:SystemInstance')[0]
    category = model.getAttribute('category')
    model_name = model.getAttribute('name')
    out_file["model_name"] = category + "_" + model_name

    features, components, connections, opas = parse_aadlmodel(model)
    Feas = getFeatures(features)

    print(Feas)
    inport_names = []
    outport_names = []
    for fea in Feas:
        if fea["type"] == "DataPort":
            if fea["direction"] == "in":
                inport_names.append(fea["name"])
            if fea["direction"] == "out":
                outport_names.append(fea["name"])
        else:
            continue
    out_file["Inport"] = inport_names
    out_file["Outport"] = outport_names

    return out_file


if __name__=="__main__":

    aadl_parser('aadl_isolette.xml', 'aadl_isolette.json')


