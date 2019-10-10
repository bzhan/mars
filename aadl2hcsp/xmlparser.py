"""Parse an AADL model in XML format, and store important information
to a dictionary (which can be outputted as a JSON file).

"""

# Use minidom to parse XML files
import xml.dom.minidom as xmldom
from aadl2hcsp import parserAnnex
import os
import json

def parseModel(model):
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
        fea['direction'] = feature.getAttribute('direction')
        fea['type'] = feature.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Feas.append(fea)
    return Feas

def getComponents(components):
    """Interpret a list of components."""
    Coms = []
    for component in components:
        if component.getAttribute('category') in ['system', 'process', 'thread', 'abstract']:
            com = {}
            com['category'] = component.getAttribute('category')
            com['name'] = component.getAttribute('name')
            #if component.getElementsByTagName('classifier'):
            if component.getElementsByTagName('componentImplementation'):
                name_impl = component.getElementsByTagName('classifier')[0].getAttribute('href').split('.')[-2]
                if com['name'] != name_impl:
                    com['name_impl'] = name_impl

            com['features'] = [node for node in component.childNodes if node.nodeName == 'featureInstance']
            com['features'] = getFeatures(com['features'])
            Coms.append(com)
    return Coms

def getConnections(connections):
    """Interpret a list of connections."""
    Conns = []
    for connection in connections:
        conn = {}
        conn['name'] = connection.getAttribute('name')
        src, dest = conn['name'].split('->')
        conn['source'] = src.strip()
        conn['destination'] = dest.strip()
        if connection.getElementsByTagName('feature'):
            conn['type'] = connection.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Conns.append(conn)
    return Conns

def getOwnedPropertyAssociation(opas, category, name, *, protocol):
    """Interpret a list of owned property associations."""
    Opas = []
    for opa in opas:
        opass = {}
        opass['name'] = opa.getElementsByTagName('property')[0].getAttribute('href').split('#')[-1]
        opass['type'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0] \
            .getAttribute('xsi:type').split(':')[-1]
        if opass['type'] == 'NamedValue':
            if category == 'process':
                assert protocol in ('HPF', 'FIFO', 'SJF'), "Wrong protocol for process."
                opass['value'] = protocol

            elif category == 'thread':
                assert protocol in ('Periodic', 'Sporadic'), "Wrong protocol for thread."
                opass['value'] = protocol

        elif opass['type'] == 'IntegerLiteral':
            opass['value'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
            .getAttribute('value')

        elif opass['type'] == 'RangeValue':
            range = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]
            opass['value'] = [range.getElementsByTagName('minimum')[0].getAttribute('value'),
                              range.getElementsByTagName('maximum')[0].getAttribute('value')]
        Opas.append(opass)
    return Opas


def aadlparser(aadlfile, dic):
    """Parse the give AADL file, add the annex info into dic."""
    AP = parserAnnex.AnnexParser()
    Annexs = AP.getAnnex(aadlfile)
    for th in Annexs.keys():
        if isinstance(Annexs[th]['Discrete'], list) and th in dic.keys():
            code = ' '.join(Annexs[th]['Discrete'])
            var, state, trans = AP.createParser(code)
            dic[th]['Annex'] = {}
            dic[th]['Annex']['var'] = var
            dic[th]['Annex']['state'] = state
            dic[th]['Annex']['trans'] = trans


def parser(xmlfile, dic, *, protocol):
    """Parse the given XML file, add the read info into dic."""
    domobj = xmldom.parse(xmlfile)
    model = domobj.getElementsByTagName('instance:SystemInstance')[0]
    category = model.getAttribute('category')
    modelname = model.getAttribute('name')
    features, components, connections, opas = parseModel(model)
    dic[modelname] = {
        'category': category,
        'name': modelname.split('_')[0],
        'features': getFeatures(features),
        'components': getComponents(components),
        'connections': getConnections(connections),
        'opas': getOwnedPropertyAssociation(opas, category, modelname.split('_')[0], protocol=protocol)
    }
