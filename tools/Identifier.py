#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os

from common.Utilities import error_exit
import Emitter
from common import Values
import Logger
import Extractor
import Finder
import Generator


def identify_missing_functions(ast_map, ast_node, source_path_b, source_path_d, skip_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tidentifying missing function calls")
    missing_function_list = dict()
    call_list = Extractor.extract_call_node_list(ast_node)
    # print(call_list)
    # print(skip_list)
    for call_expr in call_list:
        # print(call_expr)
        function_ref_node = call_expr['children'][0]
        function_name = function_ref_node['value']
        # print(function_name)
        line_number = function_ref_node['start line']
        # print(line_number)
        if line_number in skip_list:
            continue
        function_node = Finder.search_function_node_by_name(ast_map, function_name)
        # print(function_node)
        if function_node is not None:
            # print(function_node)
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
    # print(missing_function_list)
    return missing_function_list


def identify_missing_var(function_node_a, function_node_b, insert_node_b, skip_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tidentifying missing variables")
    missing_var_list = dict()
    ref_list = Extractor.extract_reference_node_list(insert_node_b)
    dec_list = Extractor.extract_decl_list(function_node_a)
    dec_node_list_b = Extractor.extract_decl_node_list(function_node_b)
    for ref_node in ref_list:
        node_type = str(ref_node['type'])
        node_start_line = int(ref_node['start line'])
        if node_start_line in skip_list:
            continue
        if node_type == "DeclRefExpr":
            ref_type = str(ref_node['ref_type'])
            identifier = str(ref_node['value'])
            if ref_type == "VarDecl":
                if identifier not in dec_list:
                    if identifier in missing_var_list.keys():
                        missing_var_list.append(identifier)
                    else:
                        info = dict()
                        info['ref_list'] = list()
                        info['ast-node'] = dec_node_list_b[identifier]
                        missing_var_list[identifier] = info
            elif ref_type == "FunctionDecl":
                if identifier in Values.STANDARD_FUNCTION_LIST:
                    continue
    return missing_var_list


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


def identify_missing_definitions(function_node, missing_function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
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
                if identifier in Values.STANDARD_FUNCTION_LIST:
                    continue
                if identifier not in missing_function_list:
                    print(identifier)
                    print(Values.STANDARD_FUNCTION_LIST)
                    error_exit("FOUND NEW DEPENDENT FUNCTION")
    return list(set(missing_definition_list))


def identify_missing_macros(ast_node, source_file, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tidentifying missing macros")
    missing_macro_list = dict()
    ref_list = Extractor.extract_reference_node_list(ast_node)
    for ref_node in ref_list:
        node_type = str(ref_node['type'])
        if node_type == "Macro":
            identifier = str(ref_node['value'])
            node_child_count = len(ref_node['children'])
            if identifier in Values.STANDARD_MACRO_LIST:
                continue
            if node_child_count:
                for child_node in ref_node['children']:
                    identifier = str(child_node['value'])
                    if identifier in Values.STANDARD_MACRO_LIST:
                        continue

                    if identifier not in missing_macro_list.keys():
                        info = dict()
                        info['source'] = source_file
                        info['target'] = target_file
                        missing_macro_list[identifier] = info
                    else:
                        error_exit("MACRO REQUIRED MULTIPLE TIMES!!")
    return missing_macro_list


def identify_missing_macros_in_func(function_node, source_file, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tidentifying missing macros")
    missing_macro_list = dict()
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
            if identifier in Values.STANDARD_MACRO_LIST:
                continue
            if node_child_count:
                for child_node in ref_node['children']:
                    identifier = str(child_node['value'])
                    if identifier in Values.STANDARD_MACRO_LIST:
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
    return missing_macro_list


def identify_insertion_points(candidate_function):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    insertion_point_list = dict()
    function_id, function_info = candidate_function
    source_path, function_name = function_id.split(":")
    start_line = int(function_info['start-line'])
    last_line = int(function_info['last-line'])
    exec_line_list = function_info['exec-lines']
    var_map = function_info['var-map']
    # don't include the last line (possible crash line)
    best_score = 0
    # print(var_map.values())
    for exec_line in exec_line_list:
        # if exec_line == last_line:
        #     continue
        Emitter.special("\t\t" + source_path + "-" + function_name + ":" + str(exec_line))
        available_var_list = Extractor.extract_variable_list(source_path,
                                                             start_line,
                                                             exec_line,
                                                             False)
        # print(source_path, start_line, exec_line, False)
        # print(available_var_list)
        unique_var_name_list = list()
        for (var_name, line_num, var_type) in available_var_list:
            if var_name not in unique_var_name_list:
                unique_var_name_list.append(var_name)

        # print(exec_line)
        # print(unique_var_name_list)
        score = len(list(set(unique_var_name_list).intersection(var_map.values())))
        Emitter.normal("\t\t\t\tscore: " + str(score))
        insertion_point_list[exec_line] = score
        if score > best_score:
            best_score = score

    return insertion_point_list, best_score


def identify_divergent_point(byte_list, sym_path_list, trace_list, stack_info):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tfinding similar location in recipient")
    length = len(sym_path_list) - 1
    count_common = len(byte_list)
    candidate_list = list()
    estimated_loc = ""
    for n in range(length, 0, -1):
        key = sym_path_list.keys()[n]
        # print(key)
        sym_path = sym_path_list[key]
        # print(sym_path)
        bytes_temp = Extractor.extract_input_bytes_used(sym_path)
        # print(bytes_temp)
        count = len(list(set(byte_list).intersection(bytes_temp)))
        # print(count_common, count)
        if count == count_common:
            candidate_list.append(key)
    length = len(trace_list) - 1
    grab_nearest = False
    # print(candidate_list)
    # print(stack_info)
    for n in range(length, 0, -1):
        trace_loc = trace_list[n]
        source_path, line_number = trace_loc.split(":")
        source_path = os.path.abspath(source_path)
        trace_loc = source_path + ":" + line_number
        if grab_nearest:
            # print(trace_loc)
            if source_path in stack_info.keys():
                info = stack_info[source_path]
                # print(info)
                found_in_stack = False
                for func_name in info:
                    line_number_stack = info[func_name]
                    if int(line_number_stack) == int(line_number):
                        found_in_stack = True
                        break
                if not found_in_stack:
                        estimated_loc = trace_loc
                        break
            elif ".c" in trace_loc:
                estimated_loc = trace_loc
                break
        else:
            if trace_loc in candidate_list:
                if source_path in stack_info.keys():
                    info = stack_info[source_path]
                    for func_name in info:
                        line_number_stack = info[func_name]
                        if int(line_number_stack) == int(line_number):
                            grab_nearest = True
                elif ".h" in source_path:
                    grab_nearest = True
                else:
                    estimated_loc = trace_loc
                    break

    return estimated_loc


def identify_fixed_errors(output_a, output_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    fixed_error_list = list()
    error_list_a = Extractor.extract_error_list_from_output(output_a)
    error_list_b = Extractor.extract_error_list_from_output(output_b)
    fixed_error_list = [error for error in error_list_a if error not in error_list_b]
    return list(set(fixed_error_list))
