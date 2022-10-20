
import json
import os
from lark import Lark, Transformer, v_args, exceptions
from lark.tree import Meta
from copy import deepcopy
from json import JSONEncoder

grammar = r"""
    
    ?var_name: CNAME -> varname_expr
            | CNAME "::" CNAME -> refer_expr
            | CNAME "." CNAME -> field_expr
            | CNAME ".imp" -> imp_expr
            | CNAME ".imp" UNITED_NUM -> namedimp_expr
            | CNAME "::" CNAME ".imp" -> refer_imp_expr
            | CNAME "::" CNAME ".imp" UNITED_NUM -> refer_namedimp_expr
    
    ?package_cmd: "package" var_name "public" (atom_cmd)* "end" var_name ";"

    ?port_feature_cmd: var_name ":" var_name var_name "port" ";"

    ?prop_value: UNITED_NUM | UNITED_NUM ".." UNITED_NUM | PROTOCOL_STRING

    ?prop_cmd: var_name "=>" prop_value ";" ->model_prop_cmd
                | var_name "=>" "(" "reference" "(" var_name ")" ")" "applies to" var_name ("," var_name)*  ";" ->system_prop_cmd

    ?device_cmd: "features" (port_feature_cmd)* "properties" (prop_cmd)* -> feat_prop_cmd
                | "features" (port_feature_cmd)* -> feat_only_cmd

    ?annex_string: PATH_STRING -> path_string
                    | LANGUAGE_STRING ->language_string

    ?deviceimp_cmd: "annex" var_name "{" annex_string "};" -> annex_cmd

    ?bus_cmd: "properties" (prop_cmd)* ->prop_only_cmd

    ?access_feature_cmd: var_name ":" "requires" var_name "access" var_name ";"

    ?processor_cmd: "features" (access_feature_cmd)* "properties" (prop_cmd)*
    
    ?process_cmd: "features" (port_feature_cmd)* -> feat_only_cmd

    ?comp_cmd: var_name ":" var_name var_name";"

    ?conn_cmd: var_name ":" "port" var_name "->" var_name ";"

    ?processimp_cmd: "subcomponents" (comp_cmd)* "connections" (conn_cmd)*

    ?thread_cmd: "features" (port_feature_cmd)* "properties" (prop_cmd)* -> feat_prop_cmd

    ?threadimp_cmd: "annex" var_name "{" annex_string "};" -> annex_cmd

    ?systemimp_cmd: "subcomponents" (comp_cmd)* "connections" (conn_cmd)* "properties" (prop_cmd)*

    ?abstract_cmd: "features" (port_feature_cmd)* -> feat_only_cmd

    ?abstractimp_cmd: "annex" var_name "{" annex_string "};" -> annex_cmd


    ?atom_cmd:  "with" var_name ";" -> with_cmd
            | "device" var_name device_cmd "end" var_name ";" -> handle_device
            | "device implementation" var_name deviceimp_cmd "end" var_name ";" -> handle_deviceimp
            | "bus" var_name bus_cmd "end" var_name ";" -> handle_bus
            | "bus implementation" var_name "end" var_name ";" -> handle_busimp
            | "processor" var_name processor_cmd "end" var_name ";" -> handle_processor
            | "process" var_name process_cmd "end" var_name ";" -> handle_process
            | "process implementation" var_name processimp_cmd "end" var_name ";" -> handle_processimp
            | "thread" var_name thread_cmd "end" var_name ";" -> handle_thread
            | "thread implementation" var_name threadimp_cmd "end" var_name ";" -> handle_threadimp
            | "system" var_name "end" var_name ";" -> handle_system
            | "system implementation" var_name systemimp_cmd "end" var_name ";"->handle_systemimp
            | "abstract" var_name abstract_cmd "end" var_name ";" ->handle_abstract
            | "abstract implementation" var_name abstractimp_cmd "end" var_name ";" ->handle_abstractimp

    %import common.CNAME
    %import common.DIGIT
    %import common.LETTER
    %import common.WS
    
    

    UNITED_NUM : (DIGIT|LETTER)+
    PATH_STRING: "**" /.*?/ /(?<!\\)(\\\\)*?/ "**"
    LANGUAGE_STRING:  "**" "(" /.*?/ /(?<!\\)(\\\\)*?/ ")** **"
        | "**" /.*?/ /(?<!\\)(\\\\)*?/  "(" /.*?/ /(?<!\\)(\\\\)*?/ ")** **"
    PROTOCOL_STRING: "(" LETTER+ ")"
    COMMENT: "--" /[^\n]*/

    %ignore WS
    %ignore COMMENT
"""


def simplifyAADL(info):
    """
    Simplify the internal representation of AADL file, mainly to
    handle issues with connections.

    """
    vars = {}
    connmap = {}
    source_conn_map = {}
    for key, value in info.items():
        if 'connmap' in value.keys():
            for k, v in value['connmap'].items():
                connmap[k] = v
        if 'source_conn_map' in value.keys():
            for k, v in value['source_conn_map'].items():
                source_conn_map[k] = v
        if(key != "connmap" and key != "connmap_rv"):
            if value["category"] == "process":
                # create connmap and connmap_rv
                for k, v in value["connections"].items():
                    if v['source'] in value["components"].keys():
                        info[key]['connections'][k]['source'] = value["components"][v['source']]
                        source = info[key]['connections'][k]['source'] + \
                            '.'+v['source_port']
                    else:
                        source = v['source']+'.'+v['source_port']
                    if v['target'] in value["components"].keys():
                        info[key]['connections'][k]['target'] = value["components"][v['target']]
                        target = info[key]['connections'][k]['target'] + \
                            '.'+v['target_port']
                    else:
                        target = v['target']+'.'+v['target_port']

                    if source not in connmap.keys():
                        connmap[source] = []
                    connmap[source].append(target)
                    if source not in source_conn_map.keys():
                        source_conn_map[source] = []
                    source_conn_map[source].append(k)

                # extract components of process(thread) to info
                pop_list = []
                temp = deepcopy(info)
                for k, v in value["components"].items():
                    pop_list.append(k)
                    temp[key]["components"][v] = info[v]
                for k in pop_list:
                    temp[key]["components"].pop(k)
                info = temp
            if value["category"] == "system":
                output = {}
                if "components" in value.keys():
                    for k, v in value["components"].items():
                        if type(v) == list:
                            vars[k] = deepcopy(info[v[0]][v[1]])
                            vars[k]['refered_name'] = v[1]
                            if info[v[0]][v[1]]["category"] != "process":
                                output[v[1]] = info[v[0]][v[1]]
                            else:
                                for threadk, threadv in info[v[0]][v[1]]["components"].items():
                                    output[threadk] = threadv
                        if type(v) == str:
                            vars[k] = deepcopy(info[v])
                            vars[k]['refered_name'] = v
                            if info[v]["category"] != "process":
                                output[k] = info[v]
                            else:
                                for threadk, threadv in info[v]["components"].items():
                                    output[threadk] = threadv
                if "connections" in value.keys():
                    for k, v in value["connections"].items():
                        source = v['source']+'.'+v['source_port']
                        target = v['target']+'.'+v['target_port']
                        if source not in connmap.keys():
                            connmap[source] = []
                        connmap[source].append(target)
                        if source not in source_conn_map.keys():
                            source_conn_map[source] = []
                        source_conn_map[source].append(k)
                if "actual_connection_binding" in value.keys():
                    for k, v in value["actual_connection_binding"].items():
                        for conn in v:
                            output[conn] = {}
                            output[conn][vars[k]['category']
                                         ] = vars[k]['refered_name']
                info = output


    # update connmap and simplify conn
    if 'connmap' not in info.keys():
        info['connmap'] = {}
    info['connmap'] .update(connmap)
    if 'source_conn_map' not in info.keys():
        info['source_conn_map'] = {}
    info['source_conn_map'] .update(source_conn_map)
    return info


def simplify_conn_in_AADL(info):
    connmap = deepcopy(info['connmap'])
    info.pop('connmap')
    while(True):
        connmap_new = {}
        ignorelist = []
        for k, v in connmap.items():
            if k not in ignorelist:
                if v[0] in connmap.keys():
                    connmap_new[k] = connmap[v[0]]
                    ignorelist.append(v[0])
                    if(v[0] in connmap_new.keys()):
                        connmap_new.pop(v[0])
                else:
                    connmap_new[k] = connmap[k]
        if connmap == connmap_new:
            break
        else:
            connmap = connmap_new
    count = 0
    for k,v in connmap.items():
        rank = 0
        for targetname in v:
            conn_name = info['source_conn_map'][k][rank]
            if conn_name not in info.keys():
                info[conn_name]={}
            sourcename = k
            [source,source_port] = sourcename.split('.')
            [target,target_port] = targetname.split('.')
            info[conn_name]['source'] = source
            info[conn_name]['source_port'] = source_port
            info[conn_name]['target'] = [target]
            info[conn_name]['target_port'] = [target_port]
            info[conn_name]['category'] = "connection"
            rank =rank+1
    info.pop('source_conn_map')
    return info


@v_args(inline=True)
class AADLTransformer(Transformer):
    def __init__(self, directory):
        self.directory = directory

    def varname_expr(self, name):
        return str(name)

    def refer_expr(self, package_name, fun_name):
        return [str(package_name), str(fun_name)]

    def field_expr(self, name, field_name):
        return[str(name), str(field_name)]

    def imp_expr(self, name):
        return str(name)

    def namedimp_expr(self, name, imp_name):
        return str(name)

    def refer_imp_expr(self, package_name, fun_name):
        return [str(package_name), str(fun_name)]

    def refer_namedimp_expr(self, package_name, fun_name, imp_name):
        return [str(package_name), str(fun_name)]

    def with_cmd(self, name):
        filename = os.path.join(self.directory, name + '.aadl')
        try:
            with open(filename, encoding='utf-8') as f:
                text = f.read()
        except FileNotFoundError:
            print('Warning: file %s not found' % filename)

        try:
            text = aadl_parser(self.directory).parse(text)
            text["category"] = "package"
            return [name, text]
        except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise ParseFileException(error_str)

    def port_feature_cmd(self, name, direction, type):
        return ['feat', {name: name}, direction]

    def prop_value(self, *args):
        return args[0]+".."+args[1]

    def model_prop_cmd(self, name, val):
        if(str(val).isdigit()):
            return ['prop', {name: int(val)}]
        else:
            val = str(val)
            val = val.replace("(", "")
            val = val.replace(")", "")
            return ['prop', {name: val}]

    def system_prop_cmd(self, name, ref_name, *args):
        text = []
        for arg in args:
            text.append(arg)
        return ['sysprop', name, ref_name, text]

    def feat_prop_cmd(self, *args):
        text = {}
        for arg in args:
            if arg[0] == 'feat':
                if arg[2] == 'out':
                    if "output" not in text.keys():
                        text["output"] = {}
                    text["output"].update(arg[1])
                if arg[2] == 'in':
                    if "input" not in text.keys():
                        text["input"] = {}
                    text["input"].update(arg[1])
            if arg[0] == 'prop':
                text.update(arg[1])
        return text

    def feat_only_cmd(self, *args):
        text = {}
        for arg in args:
            if arg[0] == 'feat':
                if arg[2] == 'out':
                    if "output" not in text.keys():
                        text["output"] = {}
                    text["output"].update(arg[1])
                if arg[2] == 'in':
                    if "input" not in text.keys():
                        text["input"] = {}
                    text["input"].update(arg[1])
        return text

    def handle_device(self, name, text, nm):
        text["category"] = "device"
        new_text = [name, text]
        return new_text

    def path_string(self, string):
        return ['path', string]

    def language_string(self, string):
        return ['language', string]

    def annex_cmd(self, name, annex_string):
        text = {"impl": name}
        if annex_string[0] == 'path':
            true_string = str(annex_string[1])
            true_string = true_string[2:-2]
            true_string = true_string.strip()
            text.update({"discrete_computation": true_string})
        if annex_string[0] == 'language':
            true_string = str(annex_string[1])
            true_string = true_string[2:-2]
            true_string = true_string.strip()
            text.update({"computation": true_string})
        return text

    def handle_deviceimp(self, name, text, nm):
        text["category"] = "device"
        return [name, text]

    def prop_only_cmd(self, *args):
        text = {}
        for arg in args:
            if arg[0] == 'prop':
                text.update(arg[1])
        return text

    def handle_bus(self, name, text, nm):
        text["category"] = "bus"
        return [name, text]

    def handle_busimp(self, name, nm):
        pass

    def access_feature_cmd(self, port_name, type, bus_name):
        return ['feat', {port_name: bus_name}]

    def processor_cmd(self, *args):
        text = {}
        for arg in args:
            text.update(arg[1])
        return text

    def handle_processor(self, name, text, nm):
        text["category"] = "processor"
        return [name, text]

    def handle_process(self, name, text, nm):
        text["category"] = "process"
        return[name, text]

    def comp_cmd(self, name, cl, comp_name):
        return ['comp', {name: comp_name}]

    def conn_cmd(self, name, from_port, target_port):
        text = {}
        if type(from_port) == str:
            text.update({"source": []})
            text.update({"source_port": from_port})
        if type(from_port) == list and len(from_port) == 2:
            text.update({"source": from_port[0]})
            text.update({"source_port": from_port[1]})
        if type(target_port) == str:
            text.update({"target": []})
            text.update({"target_port": target_port})
        if type(target_port) == list and len(target_port) == 2:
            text.update({"target": target_port[0]})
            text.update({"target_port": target_port[1]})
        return ['conn', {name: text}]

    def processimp_cmd(self, *args):
        text = {"components": {}, "connections": {}}
        for arg in args:
            if arg[0] == 'comp':
                text["components"].update(arg[1])
            if arg[0] == 'conn':
                text["connections"].update(arg[1])
        return text

    def handle_processimp(self, name, text, nm):
        text["category"] = "process"
        for key in text['connections'].keys():
            if text['connections'][key]['source'] == []:
                text['connections'][key]['source'] = name
            if text['connections'][key]['target'] == []:
                text['connections'][key]['target'] = name
        return [name, text]

    def handle_thread(self, name, text, nm):
        text["category"] = "thread"
        return[name, text]

    def threadimp_cmd(self, name, annex_string):
        text = {"impl": name}
        if annex_string[0] == 'path':
            text.update({"discrete_computation": annex_string[1]})
        if annex_string[0] == 'language':
            text.update({"computation": annex_string[1]})
        return text

    def handle_threadimp(self, name, text, nm):
        text["category"] = "thread"
        return[name, text]

    def handle_system(self, name, nm):
        pass

    def systemimp_cmd(self, *args):
        text = {"components": {}, "connections": {}}
        for arg in args:
            if arg[0] == 'comp':
                text["components"].update(arg[1])
            if arg[0] == 'conn':
                text["connections"].update(arg[1])
            if arg[0] == 'sysprop':
                if arg[1] not in text.keys():
                    text[arg[1]] = {}
                text[arg[1]].update({arg[2]: arg[3]})
        return text

    def handle_systemimp(self, name, text, nm):
        text["category"] = "system"
        return[name, text]

    def handle_abstract(self, name, text, nm):
        text["category"] = "abstract"
        return[name, text]

    def handle_abstractimp(self, name, text, nm):
        text["category"] = "abstract"
        return[name, text]

    def package_cmd(self, *args):
        text = {}
        for i in range(1, len(args)-1):
            if args[i] != None:
                if args[i][0] in text.keys():
                    text[args[i][0]].update(args[i][1])
                else:
                    text[args[i][0]] = args[i][1]
        text = simplifyAADL(text)
        return text


def aadl_parser(directory):
    """Obtain AADL parser for the given directory."""
    aadl_transformer = AADLTransformer(directory)
    return Lark(grammar, start="package_cmd", parser="lalr", transformer=aadl_transformer)


class ParseFileException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


class CompactJSONEncoder(json.JSONEncoder):
    """A JSON Encoder that puts small lists on single lines."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.indentation_level = 0

    def encode(self, o):
        """Encode JSON object *o* with respect to single line lists."""
        if isinstance(o, (list, tuple)):
            if self._is_single_line_list(o):
                return "[" + ", ".join(json.dumps(el) for el in o) + "]"
            else:
                self.indentation_level += 1
                output = [self.indent_str + self.encode(el) for el in o]
                self.indentation_level -= 1
                return "[\n" + ",\n".join(output) + "\n" + self.indent_str + "]"

        elif isinstance(o, dict):
            if self._is_single_line_dict(o):
                return "{" + ", ".join(f"{json.dumps(k)}: {self.encode(v)}" for k, v in o.items()) + "}"
            else:
                self.indentation_level += 1
                output = [self.indent_str +
                          f"{json.dumps(k)}: {self.encode(v)}" for k, v in o.items()]
                self.indentation_level -= 1
                return "{\n" + ",\n".join(output) + "\n" + self.indent_str + "}"

        else:
            return json.dumps(o)

    def _is_single_line_list(self, o):
        if isinstance(o, (list, tuple)):
            return not any(isinstance(el, (list, tuple, dict)) for el in o) \
                and len(o) <= 3 \
                and len(str(o)) - 2 <= 60

    def _is_single_line_dict(self, o):
        if isinstance(o, dict):
            return not any(isinstance(el, (list, tuple, dict)) for el in o) \
                and len(o) <= 2 \
                and len(str(o)) - 2 <= 60

    @property
    def indent_str(self) -> str:
        return " " * self.indentation_level * self.indent

    def iterencode(self, o, **kwargs):
        """Required to also work with `json.dump`."""
        return self.encode(o)


def mergedict(dict1, dict2):
    dict3 = deepcopy(dict2)
    for key, value in dict1.items():
        if key in dict2:
            if type(dict1[key]) == dict and type(dict2[key]) == dict:
                dict3[key] = mergedict(dict1[key], dict2[key])
            elif type(dict1[key]) == dict and type(dict2[key]) != dict:
                dict3[key] = dict1[key]
            elif type(dict1[key]) != dict and type(dict2[key]) == dict:
                dict3[key] = dict2[key]
            else:
                dict3[key] = dict2[key]
        else:
            dict3[key] = value
    return dict3


def convert_AADL(directory: str, startfile: str, configfile: str):
    """
    Convert AADL files in the given directory to JSON files.

    directory: str - directory containing input AADL and JSON files.
    startfile: str - starting AADL file.
    configfile: str - starting JSON configuration file.

    """
    file1 = open(os.path.join(directory, startfile), "r", encoding='utf-8')
    text = file1.read()
    file1.close()

    info = dict()
    try:
        info = aadl_parser(directory).parse(text)
    except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
        error_str = "Unable to parse\n"
        for i, line in enumerate(text.split('\n')):
            error_str += line + '\n'
            if i == e.line - 1:
                error_str += " " * (e.column-1) + "^" + '\n'
        raise ParseFileException(error_str)

    info = simplify_conn_in_AADL(info)
    with open(directory + '\\' + configfile, 'r') as f:
        config = json.load(f)

    info = mergedict(info, config)
    return info
