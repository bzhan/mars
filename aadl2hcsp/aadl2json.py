
import json
import os
from lark import Lark, Transformer, v_args, exceptions
from lark.tree import Meta


grammar = r"""

    ?package_cmd: "package" CNAME "public" (atom_cmd)* "end" CNAME

    ?port_feature_cmd: CNAME ":" CNAME CNAME "port" ";"

    ?prop_cmd: CNAME "=>" PROP_STRING ";"

    ?device_cmd: "features" (port_feature_cmd)* "properties" (prop_cmd)*

    ?deviceimp_cmd: ("annex" STRING ";")*

    ?bus_cmd: "properties" (prop_cmd)*

    ?access_feature_cmd: CNAME ":" STRING ";"

    ?processor_cmd: "features" (access_feature_cmd)* "properties" (prop_cmd)*
    
    ?process_cmd: "features" (port_feature_cmd)*

    ?comp_cmd: CNAME ":" CNAME STRING";"

    ?conn_cmd: CNAME ":" CNAME STRING "->" STRING ";"

    ?processimp_cmd: "subcomponents" (comp_cmd)* "connections" (conn_cmd)*

    ?thread_cmd: "fetures" (port_feature_cmd)* "properties" (prop_cmd)*

    ?threadimp_cmd: ("annex" CNAME ";")*

    ?system_cmd: "fetures" (port_feature_cmd)*

    ?systemimp_cmd: "subcomponents" (comp_cmd)* "connections" (conn_cmd)*

    ?atom_cmd:  "with" CNAME ";"->with_cmd
            | "device" CNAME device_cmd "end" CNAME ";" ->handle_device
            | "device implementation" CNAME deviceimp_cmd "end" CNAME ";"->handle_deviceimp
            | "bus" CNAME bus_cmd "end" CNAME ";"->handle_bus
            | "bus implementation" CNAME "end" CNAME ";"->handle_busimp
            | "processor" CNAME processor_cmd "end" CNAME ";"->handle_processor
            | "process" CNAME process_cmd "end" CNAME ";"->handle_process
            | "process implementation" CNAME processimp_cmd "end" CNAME ";"->handle_processimp
            | "thread" CNAME thread_cmd "end" CNAME ";" ->handle_thread
            | "thread implementation" CNAME threadimp_cmd "end" CNAME ";"->handle_threadimp
            | "system" CNAME system_cmd "end" CNAME ";"->handle_system
            | "system implementation" CNAME system_cmd "end" CNAME ";"->handle_systemimp

    %import common.CNAME
    %import common.WS

    PROP_STRING: /^[;]+/
    ANNEX_STRING: /^[**]+/
    %ignore WS
"""


def _vargs_meta_inline(f, _data, children, meta):
    return f(meta, *children)


@v_args(wrapper=_vargs_meta_inline)
class HPTransformer(Transformer):
    def __init__(self):
        pass

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
            return {name: aadl_parser.parse(text)}
        except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise ParseFileException(error_str)

    def feature_cmd(self, meta, name, val):
        return {name: val}

    def properties_cmd(self, meta, name, val):
        return {name: val}

    def device_cmd(self, meta, *args):
        return 0


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


def convert_AADL(path):

    file1 = open(path, "r", encoding='utf-8')
    text = file1.read()
    file1.close()

    info = dict()
    # First, read lines from file, each line containing ::= means the
    # start of a new program.
    text = text.replace("\t", "")
    try:
        js = aadl_parser.parse(text)
    except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
        error_str = "Unable to parse\n"
        for i, line in enumerate(text.split('\n')):
            error_str += line + '\n'
            if i == e.line - 1:
                error_str += " " * (e.column-1) + "^" + '\n'
        raise ParseFileException(error_str)

    output = json.dumps(info, separators=(',', ':'))

    return output
