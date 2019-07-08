#coding=utf-8

#通过minidom解析xml文件
import xml.dom.minidom as xmldom
import os
import json

dic={}
categories=['system','process','thread']
#xmlfilepath = os.path.abspath("iosolette.xml")
#print("xml文件路径：", xmlfilepath)

#path = './instances/'
#for file in os.listdir(path):
#    os.rename(os.path.join(path, file), os.path.join(path, file.split('.')[0]+ ".xml"))

def parseModel(model):
    nodes = model.childNodes
    features = [node for node in nodes if node.nodeName == 'featureInstance']
    components = [node for node in nodes if node.nodeName == 'componentInstance']
    connections = [node for node in nodes if node.nodeName == 'connectionInstance']
    opas = [node for node in nodes if node.nodeName == 'ownedPropertyAssociation']

    return features,components,connections,opas

def getFeatures(features):
    Feas=[]
    for feature in features:
        fea={}
        fea['name'] = feature.getAttribute('name')
        fea['direction'] = feature.getAttribute('direction')
        fea['type'] = feature.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Feas.append(fea)
    return Feas

def getComponents(components):
    Coms=[]
    for component in components:
        if component.getAttribute('category') in categories:
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
    Conns=[]
    for connection in connections:
        conn={}
        conn['name'] = connection.getAttribute('name')
        conn['source'] = conn['name'].split('->')[0]
        conn['destination'] = conn['name'].split('->')[-1]
        if connection.getElementsByTagName('feature'):
            conn['type'] = connection.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
        Conns.append(conn)
    return Conns


def getOwnedPropertyAssociation(opas):
    Opas=[]
    for opa in opas:
        opass={}
        opass['name'] = opa.getElementsByTagName('property')[0].getAttribute('href').split('#')[-1]
        opass['type'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
            .getAttribute('xsi:type').split(':')[-1]
        if opass['type'] == 'NamedValue':
            opass['value']= 'Periodic'    ##解析协议
        elif opass['type'] == 'IntegerLiteral':
            opass['value'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
            .getAttribute('value')
        Opas.append(opass)
    return Opas

def parser(xmlfile):
    domobj = xmldom.parse(xmlfile)
    model = domobj.getElementsByTagName('instance:SystemInstance')[0]
    modelname = model.getAttribute('name')
    category = model.getAttribute('category')
    dic[modelname] = {'category': category, 'name': modelname.split('_')[0]}
    features, components, connections, opas = parseModel(model)
    dic[modelname]['features'] = getFeatures(features)
    dic[modelname]['components'] = getComponents(components)
    dic[modelname]['connections'] = getConnections(connections)
    dic[modelname]['opas'] = getOwnedPropertyAssociation(opas)


if __name__== "__main__":
    path = './instances/'
    outfile='out.json'
    for xmlfile in os.listdir(path):
        parser(os.path.join(path, xmlfile))
    print(dic)
    with open(outfile, "w") as f_obj:
        json.dump(dic, f_obj)








