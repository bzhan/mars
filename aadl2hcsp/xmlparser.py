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
            fea['name'] = feature.getAttribute('name')
            fea['direction'] = feature.getAttribute('direction')
            fea['type'] = feature.getElementsByTagName('feature')[0].getAttribute('xsi:type').split(':')[-1]
            Feas.append(fea)
        return Feas

    def _getComponents(self, components):
        """Interpret a list of components."""
        Coms, subcom = [],[]
        for component in components:
            if component.getAttribute('category') in ['system', 'process', 'thread', 'abstract']:
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

    def _getOwnedPropertyAssociation(self, opas, category, name, *, protocol):
        """Interpret a list of owned property associations."""

        #ameValue_list={ 'SC'

        #}
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


    def _aadlparser(self, aadlfile):
        """Parse the give AADL file, add the annex info into dic."""
        AP = parserAnnex.AnnexParser()
        Annexs = AP.getAnnex(aadlfile)
        for th in Annexs.keys():
            if isinstance(Annexs[th]['Discrete'], list) and th in self.dic.keys():
                code = ' '.join(Annexs[th]['Discrete'])
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
                        'opas': self._getOwnedPropertyAssociation(opas, category, modelname.split('_')[0], protocol=protocol)
                    }
                    new_model_list[modelname] = self._getComponents(components)[1]
            model_list = new_model_list

    def parser(self, xmlfile, aadlfile, simfile):
        self._xmlparser(xmlfile, protocol="Periodic")
        self._aadlparser(aadlfile)
        self._simparser(simfile)
        return self.dic
