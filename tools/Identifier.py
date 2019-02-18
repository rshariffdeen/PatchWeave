#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os

from common.Utilities import error_exit
import Emitter
from common import Definitions
from ast import ASTGenerator
import Logger
import Extractor
import Finder
import KleeExecutor
import Filter
from tools import Collector, Generator
import Mapper


def identify_missing_functions(ast_map, ast_node, source_path_b, source_path_d, skip_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tidentifying missing function calls")
    missing_function_list = dict()
    call_list = Extractor.extract_function_call_list(ast_node)
    for call_expr in call_list:
        function_ref_node = call_expr['children'][0]
        function_name = function_ref_node['value']
        line_number = function_ref_node['start line']
        if line_number in skip_list:
            continue
        function_node = Finder.search_function_node_by_name(ast_map, function_name)
        if function_node is not None:
            if function_name not in missing_function_list.keys():
                info = dict()
                info['node_id'] = function_node['id']
                info['source_b'] = source_path_b
                info['source_d'] = source_path_d
                missing_function_list[function_name] = info
            else:
                info = dict()
                info['node_id'] = function_node['id']
                info['source_b'] = source_path_b
                info['source_d'] = source_path_d
                if info != missing_function_list[function_name]:
                    print(missing_function_list[function_name])
                    error_exit("MULTIPLE FUNCTION REFERENCES ON DIFFERENT TARGETS FOUND!!!")
    return missing_function_list


def identify_missing_headers(function_node, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    missing_header_list = dict()
    function_definition = function_node['value']
    function_name = function_node['identifier']
    return_type = (function_definition.replace(function_name, "")).split("(")[1]
    if return_type.strip() == "_Bool":
        if "stdbool.h" not in missing_header_list.keys():
            missing_header_list["stdbool.h"] = target_file
        else:
            error_exit("UNKNOWN RETURN TYPE")
    return missing_header_list


def identify_missing_definitions(function_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_function_list
    Emitter.normal("\tidentifying missing definitions")
    missing_definition_list = list()
    ref_list = Extractor.extract_reference_node_list(function_node)
    dec_list = Extractor.extract_decl_list(function_node)
    function_identifier = function_node['identifier']
    for ref_node in ref_list:
        node_type = str(ref_node['type'])
        if node_type == "DeclRefExpr":
            ref_type = str(ref_node['ref_type'])
            identifier = str(ref_node['value'])
            if ref_type == "VarDecl":
                if identifier not in dec_list:
                    missing_definition_list.append(identifier)
            elif ref_type == "FunctionDecl":
                if identifier in Definitions.STANDARD_FUNCTION_LIST:
                    continue
                if identifier not in missing_function_list:
                    print(identifier)
                    print(Definitions.STANDARD_FUNCTION_LIST)
                    error_exit("FOUND NEW DEPENDENT FUNCTION")
    return list(set(missing_definition_list))


def identify_missing_macros(function_node, source_file, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_function_list, missing_macro_list
    Emitter.normal("\tidentifying missing macros")
    ref_list = Extractor.extract_reference_node_list(function_node)
    dec_list = Extractor.extract_decl_list(function_node)
    function_identifier = function_node['identifier']
    for ref_node in ref_list:
        node_type = str(ref_node['type'])
        if node_type == "Macro":
            identifier = str(ref_node['value'])
            node_child_count = len(ref_node['children'])
            if function_identifier in identifier or "(" in identifier:
                continue
            if identifier in Definitions.STANDARD_MACRO_LIST:
                continue
            if node_child_count:
                for child_node in ref_node['children']:
                    identifier = str(child_node['value'])
                    if identifier in Definitions.STANDARD_MACRO_LIST:
                        continue
                    if identifier not in dec_list:
                        if identifier not in missing_macro_list.keys():
                            info = dict()
                            info['source'] = source_file
                            info['target'] = target_file
                            missing_macro_list[identifier] = info
                        else:
                            error_exit("MACRO REQUIRED MULTIPLE TIMES!!")

            else:
                if identifier not in dec_list:
                    token_list = identifier.split(" ")
                    for token in token_list:
                        if token in ["/", "+", "-"]:
                            continue
                        if token not in dec_list:
                            if identifier not in missing_macro_list.keys():
                                info = dict()
                                info['source'] = source_file
                                info['target'] = target_file
                                missing_macro_list[token] = info
                            else:
                                error_exit("MACRO REQUIRED MULTIPLE TIMES!!")


def get_definition_insertion_point(source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    file_name = source_path.split("/")[-1]
    ast_node = ASTGenerator.get_ast_json(source_path)
    for child_node in ast_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "FunctionDecl":
            child_node_file_name = child_node['file']
            if child_node_file_name == file_name:
                return int(child_node['start line'])
    return -1


def get_best_insertion_point(insertion_point_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    return insertion_point_list[0]


def identify_insertion_points(estimated_loc, var_expr_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    insertion_point_list = list()
    function_list = Generator.generate_candidate_function_list(estimated_loc, var_expr_map)

    for function_id in function_list:
        source_path, function_name = function_id.split(":")
        info = function_list[function_id]
        start_line = int(info['begin-line'])
        last_line = int(info['last-line'])
        exec_line_list = info['exec-lines']
        # don't include the last line (possible crash line)
        for exec_line in exec_line_list:
            # if exec_line == last_line:
            #     continue
            insertion_point_list.append(source_path + ":" + str(exec_line))
    return insertion_point_list


def identify_divergent_point(byte_list, sym_path, trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tfinding similar location in recipient")
    length = len(sym_path) - 1
    count_common = len(byte_list)
    candidate_list = list()
    estimated_loc = ""
    for n in range(length, 0, -1):
        key = sym_path[n]
        sym_path = sym_path[key]
        bytes_temp = Mapper.get_input_bytes_used(sym_path)
        count = len(list(set(byte_list).intersection(bytes_temp)))
        if count == count_common:
            candidate_list.append(key)
    length = len(trace_list) - 1
    grab_nearest = False
    for n in range(length, 0, -1):
        path = trace_list[n]
        path = os.path.abspath(path)
        if grab_nearest:
            if ".c" in path:
                estimated_loc = path
                break
        else:
            if path in candidate_list:
                if ".h" in path:
                    grab_nearest = True
                else:
                    estimated_loc = path
                    break
    return estimated_loc
