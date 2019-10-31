"""Parse an AADL model in XML format, and store important information
to a dictionary (which can be outputted as a JSON file).

"""

# Use minidom to parse XML files
import xml.dom.minidom as xmldom
from aadl2hcsp import parserAnnex

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.MathOperations.product import Product
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SubSystems.subsystem import Subsystem
from ss2hcsp.sl.sl_diagram import SL_Diagram

from ss2hcsp.sl.get_hcsp import get_hcsp

class Parser:
    def __init__(self):
        self.dic = {}

    def _parseModel(self, model):
        """Return instances of the model separated by type."""
        nodes = model.childNodes
        features = [node for node in nodes if node.nodeName == 'featureInstance']
        components = [node for node in nodes if node.nodeName == 'componentInstance']
        connections = [node for node in nodes if node.nodeName == 'connectionInstance']
        opas = [node for node in nodes if node.nodeName == 'ownedPropertyAssociation']

        return features, components, connections, opas

    def _getFeatures(self, features):
        """Interpret a list of features."""
        Feas = []
        for feature in features:
            fea = {}
            if feature.getAttribute('category'):
                fea['category'] = feature.getAttribute('category')
            fea['name'] = feature.getAttribute('name')
            fea['direction'] = feature.getAttribute('direction')
            fea['type'] = feature.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
            if fea['type'] == "SubprogramAccess":
                fea['opas'] = self._getOwnedPropertyAssociation([node for node in feature.childNodes if node.nodeName == 'ownedPropertyAssociation'])
            Feas.append(fea)
        return Feas

    def _getComponents(self, components):
        """Interpret a list of components."""
        Coms, subcom = [],[]
        for component in components:
            if component.getAttribute('category') in ['system', 'process', 'thread', 'abstract', 'processor', 'subprogram']:
                com = {}
                subcom.append(component)
                com['category'] = component.getAttribute('category')
                com['name'] = component.getAttribute('name')
                #if component.getElementsByTagName('classifier'):
                if component.getElementsByTagName('componentImplementation'):
                    name_impl = component.getElementsByTagName('classifier')[0].getAttribute('href').split('.')[-2]
                    if com['name'] != name_impl:
                        com['name_impl'] = name_impl

                Coms.append(com)
        return Coms, subcom

    def _getConnections(self, connections):
        """Interpret a list of connections.(port, subprogram access)"""
        Conns = []
        for connection in connections:
            conn = {}
            conn['name'] = connection.getAttribute('name')
            conn['kind'] = connection.getAttribute('kind')
            src, dest = conn['name'].split('->')
            conn['source'] = src.strip()
            conn['destination'] = dest.strip()
            if connection.getElementsByTagName('feature'):
                conn['type'] = connection.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
            Conns.append(conn)
        return Conns

    def _getOwnedPropertyAssociation(self, opas):
        """Interpret a list of owned property associations."""

        protocol_list ={ 'Thread_Properties.Dispatch_Protocol':{  '0':'Periodic',
                                                                  '1':'Sporadic',
                                                                  '2': 'Aperiodic',
                                                                  '3': 'Timed',
                                                                  '4': 'Hybrid',
                                                                  '5': 'Background'},
                         'Deployment_Properties.Scheduling_Protocol':{  '0':'FIFO', #Static
                                                                        '1':'Round_Robin_Protocol',
                                                                        '2':'HPF', #POSIX_1003_HIGHEST_PRIORITY_FIRDT_PROTOCOL
                                                                        '3':'FixTimeline',
                                                                        '4':'Cooperative',
                                                                        '5':'RMS',
                                                                        '6':'DMS',
                                                                        '7':'EDF',
                                                                        '8':'SporadicServer',
                                                                        '9':'SlackServer',
                                                                        '10':'ARINC653'},
                         'Behavior_Properties.Subprogram_Call_Protocol':{'0':'HSER',
                                                                         '1':'LSER',
                                                                         '2':'ASER'}}
        Opas = []
        for opa in opas:
            opass = {}
            opass['name'] = opa.getElementsByTagName('property')[0].getAttribute('href').split('#')[-1]
            opass['type'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0] \
                .getAttribute('xsi:type').split(':')[-1]
            if opass['type'] == 'NamedValue':
                index = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0].getElementsByTagName('namedValue')[0] \
                .getAttribute('href').split('.')[-1]
                opass['value'] = protocol_list[opass['name']][index]

            elif opass['type'] == 'ListValue':
                try:
                    index = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0].getElementsByTagName(
                        'ownedListElement')[0].getElementsByTagName('namedValue')[0].getAttribute('href').split('.')[-1]
                    opass['value'] = protocol_list[opass['name']][index]
                except:
                    map_id = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0].getElementsByTagName(
                        'ownedListElement')[0].getElementsByTagName('path')[0].getElementsByTagName('namedElement')[0].getAttribute('href').split('/')[-1]
                    opass['map_id'] = map_id

            elif opass['type'] == 'IntegerLiteral':
                opass['value'] = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]\
                .getAttribute('value')

            elif opass['type'] == 'RangeValue':
                range = opa.getElementsByTagName('ownedValue')[0].getElementsByTagName('ownedValue')[0]
                opass['value'] = [range.getElementsByTagName('minimum')[0].getAttribute('value'),
                                  range.getElementsByTagName('maximum')[0].getAttribute('value')]
            Opas.append(opass)
        return Opas


    def _aadlparser(self, aadlfile):
        """Parse the give AADL file, add the annex info into dic."""
        AP = parserAnnex.AnnexParser()
        Annexs = AP.getAnnex(aadlfile)
        for th in Annexs.keys():
            if isinstance(Annexs[th]['Discrete'], list) and th in self.dic.keys():
                code = ' '.join(Annexs[th]['Discrete']).lower()
                var, state, trans = AP.createParser(code)
                self.dic[th]['Annex'] = {}
                self.dic[th]['Annex']['var'] = var
                self.dic[th]['Annex']['state'] = state
                self.dic[th]['Annex']['trans'] = trans

    def _simparser(self, simfile):
            diagram = SL_Diagram(simfile)
            model_name = diagram.parse_xml()
            diagram.add_line_name()
            diagram.comp_inher_st()
            diagram.inherit_to_continuous()
            for block in self.dic.keys():
                if block == model_name:
                    self.dic[block]['Sim'] = [str(hp) for _, hp in get_hcsp(*diagram.seperate_diagram()).hps]


    def _xmlparser(self, xmlfile, protocol):
        """Parse the given XML file, add the read info into dic."""
        domobj = xmldom.parse(xmlfile)
        model = domobj.getElementsByTagName('instance:SystemInstance')[0]
        model_list = {'': [model]}

        while len(model_list) > 0:
            new_model_list = {}
            for parent, children in model_list.items():
                for model in children:
                    category = model.getAttribute('category')
                    modelname = model.getAttribute('name').split('_')[0]
                    features, components, connections, opas = self._parseModel(model)
                    self.dic[modelname] = {
                        'category': category,
                        'parent': parent,
                        'features': self._getFeatures(features),
                        'components': self._getComponents(components)[0],
                        'connections': self._getConnections(connections),
                        'opas': self._getOwnedPropertyAssociation(opas)
                    }
                    new_model_list[modelname] = self._getComponents(components)[1]
            model_list = new_model_list

    def parser(self, xmlfile, aadlfile, simfile):
        self._xmlparser(xmlfile, protocol="Periodic")
        self._aadlparser(aadlfile)
        self._simparser(simfile)
        return self.dic
