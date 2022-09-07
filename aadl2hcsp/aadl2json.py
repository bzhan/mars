
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


def _vargs_meta_inline(f, _data, children, meta):
    return f(meta, *children)


def simplize(info):
    vars = {}
    for key, value in info.items():
        if value["category"] == "process":
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
                connmap = {}
                connmap_rv = {}
                if source not in connmap.keys():
                    connmap[source] = []
                connmap[source].append(target)
                if target not in connmap_rv.keys():
                    connmap_rv[target] = []
                connmap_rv[target].append(source)
                if 'connmap' not in info[key].keys():
                    info[key]['connmap'] = {}
                info[key]['connmap'] .update(connmap)
                if 'connmap_rv' not in info[key].keys():
                    info[key]['connmap_rv'] = {}
                info[key]['connmap_rv'] .update(connmap_rv)
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
                    output[k] = {}
                    if vars[v['source']]['category'] == 'process':
                        source = v['source']+"."+v['source_port']
                        sources = vars[v['source']]['connmap_rv'][source]
                        source = []
                        source_port = []
                        for sou in sources:
                            [s, s_port] = sou.split(".")
                            source.append(s)
                            source_port.append(s_port)
                    else:
                        source = v['source']
                        source_port = v['source_port']
                    if vars[v['target']]['category'] == 'process':
                        target = v['target']+"."+v['target_port']
                        targets = vars[v['target']]['connmap'][target]
                        target = []
                        target_port = []
                        for tar in targets:
                            [t, t_port] = tar.split(".")
                            target.append(t)
                            target_port.append(t_port)
                    else:
                        target = v['target']
                        target_port = v['target_port']
                    output[k]['source'] = source
                    output[k]['source_port'] = source_port
                    output[k]['target'] = target
                    output[k]['target_port'] = target_port
                    output[k]["category"] = "connection"
            if "actual_connection_binding" in value.keys():
                for k, v in value["actual_connection_binding"].items():
                    for conn in v:
                        output[conn][vars[k]['category']
                                     ] = vars[k]['refered_name']
            info = output

    return info


@v_args(wrapper=_vargs_meta_inline)
class HPTransformer(Transformer):
    def __init__(self):
        pass

    def varname_expr(self, meta, name):
        return str(name)

    def refer_expr(self, meta, package_name, fun_name):
        return [str(package_name), str(fun_name)]

    def field_expr(self, meta, name, field_name):
        return[str(name), str(field_name)]

    def imp_expr(self, meta, name):
        return str(name)

    def namedimp_expr(self, meta, name, imp_name):
        return str(name)

    def refer_imp_expr(self, meta, package_name, fun_name):
        return [str(package_name), str(fun_name)]

    def refer_namedimp_expr(self, meta, package_name, fun_name, imp_name):
        return [str(package_name), str(fun_name)]

    def with_cmd(self, meta, name):
        hcsp_import_path = [
            './ss2hcsp/common',
        ]
        # Read additional import path from import_path.txt
        try:
            hcsp_import_path = [os.path.abspath(
                path) for path in hcsp_import_path]
            with open('./ss2hcsp/import_path.txt') as f:
                for line in f.readlines():
                    hcsp_import_path.append(os.path.abspath(line.strip()))
        except FileNotFoundError:
            pass
            # print('Warning: import_path.txt not found.')
        for path in reversed(hcsp_import_path):
            try:
                with open(os.path.join(path, name+'.aadl'), encoding='utf-8') as f:
                    text = f.read()
            except FileNotFoundError:
                pass
        try:
            text = text.replace("\t", "")
            text = aadl_parser.parse(text)
            text["category"] = "package"
            return [name, text]
        except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise ParseFileException(error_str)

    def port_feature_cmd(self, meta, name, direction, type):
        return ['feat', {name: name}, direction]

    def prop_value(self, *args):
        return args[1]+".."+args[2]

    def model_prop_cmd(self, meta, name, val):
        if(str(val).isdigit()):
            return ['prop', {name: int(val)}]
        else:
            val = str(val)
            val = val.replace("(","")
            val = val.replace(")","")
            return ['prop', {name: val}]

    def system_prop_cmd(self, meta, name, ref_name, *args):
        text = []
        for arg in args:
            text.append(arg)
        return ['sysprop', name, ref_name, text]

    def feat_prop_cmd(self, meta, *args):
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

    def feat_only_cmd(self, meta, *args):
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

    def handle_device(self, meta, name, text, nm):
        text["category"] = "device"
        new_text = [name, text]
        return new_text

    def path_string(self, meta, string):
        return ['path', string]

    def language_string(self, meta, string):
        return ['language', string]

    def annex_cmd(self, meta, name, annex_string):
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

    def handle_deviceimp(self, meta, name, text, nm):
        text["category"] = "device"
        return [name, text]

    def prop_only_cmd(self, meta, *args):
        text = {}
        for arg in args:
            if arg[0] == 'prop':
                text.update(arg[1])
        return text

    def handle_bus(self, meta, name, text, nm):
        text["category"] = "bus"
        return [name, text]

    def handle_busimp(self, meta, name, nm):
        pass

    def access_feature_cmd(self, meta, port_name, type, bus_name):
        return ['feat', {port_name: bus_name}]

    def processor_cmd(self, meta, *args):
        text = {}
        for arg in args:
            text.update(arg[1])
        return text

    def handle_processor(self, meta, name, text, nm):
        text["category"] = "processor"
        return [name, text]

    def handle_process(self, meta, name, text, nm):
        text["category"] = "process"
        return[name, text]

    def comp_cmd(self, meta, name, cl, comp_name):
        return ['comp', {name: comp_name}]

    def conn_cmd(self, meta, name, from_port, target_port):
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

    def processimp_cmd(self, meta, *args):
        text = {"components": {}, "connections": {}}
        for arg in args:
            if arg[0] == 'comp':
                text["components"].update(arg[1])
            if arg[0] == 'conn':
                text["connections"].update(arg[1])
        return text

    def handle_processimp(self, meta, name, text, nm):
        text["category"] = "process"
        for key in text['connections'].keys():
            if text['connections'][key]['source'] == []:
                text['connections'][key]['source'] = name
            if text['connections'][key]['target'] == []:
                text['connections'][key]['target'] = name
        return [name, text]

    def handle_thread(self, meta, name, text, nm):
        text["category"] = "thread"
        return[name, text]

    def threadimp_cmd(self, meta, name, annex_string):
        text = {"impl": name}
        if annex_string[0] == 'path':
            text.update({"discrete_computation": annex_string[1]})
        if annex_string[0] == 'language':
            text.update({"computation": annex_string[1]})
        return text

    def handle_threadimp(self, meta, name, text, nm):
        text["category"] = "thread"
        return[name, text]

    def handle_system(self, meta, name, nm):
        pass

    def systemimp_cmd(self, meta, *args):
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

    def handle_systemimp(self, meta, name, text, nm):
        text["category"] = "system"
        return[name, text]

    def handle_abstract(self, meta, name, text, nm):
        text["category"] = "abstract"
        return[name, text]

    def handle_abstractimp(self, meta, name, text, nm):
        text["category"] = "abstract"
        return[name, text]

    def package_cmd(self, meta, *args):
        text = {}
        for i in range(1, len(args)-1):
            if args[i] != None:
                if args[i][0] in text.keys():
                    text[args[i][0]].update(args[i][1])
                else:
                    text[args[i][0]] = args[i][1]
        text = simplize(text)
        return text


aadl_transformer = HPTransformer()


aadl_parser = Lark(grammar, start="package_cmd",
                   parser="lalr", transformer=aadl_transformer)


# Variants of the parsers without internal transformer, returning a Lark Tree instead of a HCSP expression.
# They allow us to get meta information about line and character numbers of the parsed code.

aadl_tree_parser = Lark(grammar, start="atom_cmd",
                        parser="lalr", propagate_positions=True)


def parse_aadl_with_meta(text): return aadl_transformer.transform(
    aadl_tree_parser.parse(text))


class ParseFileException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


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
            self.indentation_level += 1
            output = [self.indent_str +
                      f"{json.dumps(k)}: {self.encode(v)}" for k, v in o.items()]
            self.indentation_level -= 1
            return "{\n" + ",\n".join(output) + "\n" + self.indent_str + "}"

        else:
            return json.dumps(o)

    def _is_single_line_list(self, o):
        if isinstance(o, (list, tuple)):
            return not any(isinstance(el, (list, tuple, dict)) for el in o)\
                and len(o) <= 2\
                and len(str(o)) - 2 <= 60

    @property
    def indent_str(self) -> str:
        return " " * self.indentation_level * self.indent

    def iterencode(self, o, **kwargs):
        """Required to also work with `json.dump`."""
        return self.encode(o)

def mergedict(dict1,dict2):
    dict3 =deepcopy(dict2)
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

def convert_AADL(path1,path2):

    file1 = open(path1, "r", encoding='utf-8')
    text = file1.read()
    file1.close()

    info = dict()
    # First, read lines from file, each line containing ::= means the
    # start of a new program.
    text = text.replace("\t", "")
    try:
        info = aadl_parser.parse(text)
    except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
        error_str = "Unable to parse\n"
        for i, line in enumerate(text.split('\n')):
            error_str += line + '\n'
            if i == e.line - 1:
                error_str += " " * (e.column-1) + "^" + '\n'
        raise ParseFileException(error_str)

    with open(path2, 'r') as f:
            config = json.load(f)

    info = mergedict(info,config)
        
    output = json.dumps(info, separators=(',', ': '),
                        indent=4, cls=CompactJSONEncoder)

    return output
