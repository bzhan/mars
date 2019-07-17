"""Parse an AADL model in XML format, and store important information
to a dictionary (which can be outputted as a JSON file).

"""

# Use minidom to parse XML files
import xml.dom.minidom as xmldom
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
        if component.getAttribute('category') in ['system', 'process', 'thread']:
            com = {}
            com['category'] = component.getAttribute('category')
            com['name'] = component.getAttribute('name')
            if component.getElementsByTagName('classifier'):
                name_impl = component.getElementsByTagName('classifier')[0].getAttribute('href').split('.')[-1]
                if com['name']!=name_impl:
                    com['name_impl']=name_impl

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
        conn['source'] = conn['name'].split('->')[0]
        conn['destination'] = conn['name'].split('->')[-1]
        if connection.getElementsByTagName('feature'):
            conn['type'] = connection.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Conns.append(conn)
    return Conns


def getOwnedPropertyAssociation(opas, category, name):
    """Interpret a list of owned property associations."""
    Opas = []
    for opa in opas:
        opass = {}
        opass['name'] = opa.getElementsByTagName('property')[0].getAttribute('href').split('#')[-1]
        opass['type'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
            .getAttribute('xsi:type').split(':')[-1]
        if opass['type'] == 'NamedValue':
            print('AAA')
            if category == 'process':
                while 1:
                    print("Please input the Scheduling Protocal apply to Process '%s'\n (0:HPF \t 1:FIFO \t 2:SJF)\n" %(name))
                    s = input("Enter your input: ")
                    if s == '0':
                        opass['value'] = 'HPF'
                        break
                    elif s == '1':
                        opass['value'] = 'FIFO'
                        break
                    elif s == '2':
                        opass['value'] = 'SJF'
                        break
                    else:
                        print('Error input ! \n Please input again ...\n')

            elif category == 'thread':
                while 1:
                    print("Please input the Dispatch Protocal apply to Thread '%s'\n (0:Periodic \t 1:Sporadic )\n" %(name))
                    s = input("Enter your input: ")
                    if s == '0':
                        opass['value'] = 'Periodic'
                        break
                    elif s == '1':
                        opass['value'] = 'Sporadic'
                        break
                    else:
                        print('Error input ! \n Please input again ...\n')
                #opass['value'] = 'Periodic'    # Parse the protocol
        elif opass['type'] == 'IntegerLiteral':
            opass['value'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
            .getAttribute('value')
        Opas.append(opass)
    return Opas

def parser(xmlfile, dic):
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
        'opas': getOwnedPropertyAssociation(opas, category, modelname.split('_')[0])
    }
