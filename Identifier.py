#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, backup_file, show_partial_diff, get_code
import Output
import Common
import Logger
import Concolic
import Generator
import Differ
import Tracer
import Mapper
import Fixer


def get_function_map(source_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tcollecting function list from source files ...")
    source_function_map = dict()
    for source_path in source_list:
        if source_path in source_function_map.keys():
            continue
        try:
            function_list, definition_list = Generator.parse_ast(source_path, False)
            source_function_map[source_path] = function_list
        except Exception as e:
            error_exit(e, "Error in parse_ast.")

    return source_function_map


def get_source_lines_from_trace(trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\t\textracting source lines executed ...")
    unique_trace_list = list(set(trace_list))
    source_line_map = dict()
    for trace_line in unique_trace_list:
        source_path, line_number = str(trace_line).split(":")
        if source_path not in source_line_map.keys():
            source_line_map[source_path] = list()
        source_line_map[source_path].append(int(line_number))
    return source_line_map


def extract_trace_function_list(source_function_map, trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\textracting function list from trace ...")
    trace_function_info = dict()
    source_line_map = get_source_lines_from_trace(trace_list)
    for source_path in source_line_map:
        function_list = source_function_map[source_path]
        trace_line_list = source_line_map[source_path]
        for line_number in trace_line_list:
            for function_name, begin_line, finish_line in function_list:
                if line_number in range(begin_line, finish_line):
                    function_id = source_path + ":" + function_name
                    if function_id not in trace_function_info.keys():
                        trace_function_info[function_id] = dict()
                        trace_function_info[function_id]['start'] = begin_line
                        trace_function_info[function_id]['end'] = finish_line
                        trace_function_info[function_id]['last'] = int(line_number)
                        trace_function_info[function_id]['begin'] = int(line_number)
                        trace_function_info[function_id]['lines'] = list()
                        trace_function_info[function_id]['lines'].append(line_number)
                    else:
                        if line_number not in trace_function_info[function_id]['lines']:
                            trace_function_info[function_id]['lines'].append(line_number)
                        if trace_function_info[function_id]['last'] < line_number:
                            trace_function_info[function_id]['last'] = line_number
                        if trace_function_info[function_id]['begin'] > line_number:
                            trace_function_info[function_id]['begin'] = line_number
                    break
    return trace_function_info


def filter_trace_list(trace_list, estimate_loc):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tfiltering trace based on estimation point")
    filtered_trace_list = list()
    # print(trace_list)
    # print(estimate_loc)
    for n in range(len(trace_list) - 1, 0, -1):
        filtered_trace_list.append(trace_list[n])
        if estimate_loc == trace_list[n]:
            break
    filtered_trace_list.reverse()
    # print(filtered_trace_list)
    return filtered_trace_list


def generate_candidate_function_list(estimate_loc, var_expr_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating candidate functions")
    filtered_trace_list = filter_trace_list(Tracer.list_trace_c, estimate_loc)
    source_list_c = extract_source_list(filtered_trace_list)
    source_function_map = get_function_map(source_list_c)
    trace_function_list = extract_trace_function_list(source_function_map, filtered_trace_list)
    candidate_function_list = dict()
    for function_id in trace_function_list:
        source_path, function_name = str(function_id).split(":")
        function_info = trace_function_list[function_id]
        begin_line = function_info['begin']
        last_line = function_info['last']
        ast_map_c = Generator.get_ast_json(source_path)
        # print(int(last_line), source_path)
        function_node = get_fun_node(ast_map_c, int(last_line), source_path)
        # print(function_node)
        Mapper.generate_symbolic_expressions(source_path, last_line, last_line, FILE_VAR_EXPR_LOG_C, False)
        sym_expr_map = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_C)
        var_map = Mapper.generate_mapping(var_expr_map, sym_expr_map)
        function_id = source_path + ":" + function_name
        info = dict()
        info['var-map'] = var_map
        info['begin-line'] = begin_line
        info['last-line'] = last_line
        info['exec-lines'] = function_info['lines']
        info['score'] = len(var_map)
        candidate_function_list[function_id] = info
    return candidate_function_list


def estimate_divergent_point(byte_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tfinding similar location in recipient")
    length = len(Concolic.sym_path_c.keys()) - 1
    count_common = len(byte_list)
    candidate_list = list()
    estimated_loc = ""
    for n in range(length, 0, -1):
        key = Concolic.sym_path_c.keys()[n]
        sym_path = Concolic.sym_path_c[key]
        bytes_temp = Mapper.get_input_bytes_used(sym_path)
        count = len(list(set(byte_list).intersection(bytes_temp)))
        if count == count_common:
            candidate_list.append(key)
    length = len(Tracer.list_trace_c) - 1
    grab_nearest = False
    for n in range(length, 0, -1):
        path = Tracer.list_trace_c[n]
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


def get_sym_path(source_location):
    sym_path = ""
    if Common.VALUE_PATH_A in source_location:
        for path in Tracer.list_trace_a:
            if path in Concolic.sym_path_a.keys():
                sym_path = Concolic.sym_path_a[path]
            if path == source_location:
                break
    elif Common.VALUE_PATH_B in source_location:
        for path in Tracer.list_trace_b:
            if path in Concolic.sym_path_b.keys():
                sym_path = Concolic.sym_path_b[path]
            if path == source_location:
                break
    elif Common.VALUE_PATH_C in source_location:
        for path in Tracer.list_trace_c:
            if path in Concolic.sym_path_c.keys():
                sym_path = Concolic.sym_path_c[path]
            if path == source_location:
                break
    return sym_path


def compute_common_bytes(div_source_loc):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tanalysing common bytes in symbolic paths")
    div_sympath = get_sym_path(div_source_loc)
    common_byte_list = list()
    if Concolic.sym_path_c:
        last_sympath_c = Concolic.sym_path_c[Concolic.sym_path_c.keys()[-1]]
        # model_a = Mapper.get_model_from_solver(div_sympath)
        bytes_a = Mapper.get_input_bytes_used(div_sympath)
        # model_c = Mapper.get_model_from_solver(last_sympath_c)
        bytes_c = Mapper.get_input_bytes_used(last_sympath_c)
        common_byte_list = list(set(bytes_a).intersection(bytes_c))
    return common_byte_list


def translate_patch(patch_code, var_map):
    for var in var_map.keys():
        if var in patch_code:
            str(patch_code).replace(var, var_map[var])
    return patch_code


def insert_patch(patch_code, source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global modified_source_list
    content = ""
    if source_path not in modified_source_list:
        modified_source_list.append(source_path)
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            existing_statement = content[line_number]
            content[line_number] = patch_code + existing_statement

    with open(source_path, 'w') as source_file:
        source_file.writelines(content)


def get_ast_node_by_id(ast_node, find_id):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    is_high = False
    is_low = False
    prev_child_node = None
    node_id = int(ast_node['id'])
    if node_id == find_id:
        return ast_node

    for child_node in ast_node['children']:
        child_id = int(child_node['id'])
        if child_id == find_id:
            return child_node
        elif child_id < find_id:
            is_low = True
        else:
            is_high = True

        if is_low and is_high:
            return get_ast_node_by_id(prev_child_node, int(find_id))
        else:
            prev_child_node = child_node

    return get_ast_node_by_id(prev_child_node, int(find_id))


def get_node_str(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_str = ""
    node_type = str(ast_node['type'])
    if node_type in ["DeclStmt", "DeclRefExpr", "VarDecl"]:
        node_str = str(ast_node['value'])
    if str(ast_node['type']) == "BinaryOperator":
        operator = str(ast_node['value'])
        right_operand = get_node_str(ast_node['children'][1])
        left_operand = get_node_str(ast_node['children'][0])
        return left_operand + " " + operator + " " + right_operand
    return node_str


def output_var_map(var_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    content = ""
    for var in var_map:
        content += var + ":" + var_map[var] + "\n"
    with open(FILE_VAR_MAP, 'w') as map_file:
        map_file.writelines(content)


def output_skip_list(skip_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    content = "0\n"
    for line_number in skip_list:
        content += str(line_number) +  "\n"
    with open(FILE_SKIP_LIST, 'w') as map_file:
        map_file.writelines(content)


def output_ast_script(ast_script):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    with open(FILE_AST_SCRIPT, 'w') as script_file:
        script_file.writelines(ast_script)




def show_final_patch(source_path_a, source_path_b, source_path_c, source_path_d):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())




def identify_missing_functions(ast_node, source_path_b, source_path_d, skip_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tidentifying missing function calls")
    global missing_function_list
    call_list = extract_function_calls(ast_node)
    for call_expr in call_list:
        function_ref_node = call_expr['children'][0]
        function_name = function_ref_node['value']
        line_number = function_ref_node['start line']
        if line_number in skip_list:
            continue
        function_node_id = get_function_node_id(ast_map_a, function_name)
        if function_node_id != -1:
            if function_name not in missing_function_list.keys():
                info = dict()
                info['node_id'] = function_node_id
                info['source_b'] = source_path_b
                info['source_d'] = source_path_d
                missing_function_list[function_name] = info
            else:
                info = dict()
                info['node_id'] = function_node_id
                info['source_b'] = source_path_b
                info['source_d'] = source_path_d

                if info != missing_function_list[function_name]:
                    print(missing_function_list[function_name])
                    error_exit("MULTIPLE FUNCTION REFERENCES ON DIFFERENT TARGETS FOUND!!!")


def identify_missing_headers(function_node, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_header_list
    function_definition = function_node['value']
    function_name = function_node['identifier']
    return_type = (function_definition.replace(function_name, "")).split("(")[1]
    if return_type.strip() == "_Bool":
        if "stdbool.h" not in missing_header_list.keys():
            missing_header_list["stdbool.h"] = target_file
        else:
            error_exit("UNKNOWN RETURN TYPE")


def identify_missing_definitions(function_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_function_list
    Output.normal("\tidentifying missing definitions")
    missing_definition_list = list()
    ref_list = extract_reference_node_list(function_node)
    dec_list = extract_decl_list(function_node)
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
                if identifier in Common.STANDARD_FUNCTION_LIST:
                    continue
                if identifier not in missing_function_list:
                    print(identifier)
                    print(Common.STANDARD_FUNCTION_LIST)
                    error_exit("FOUND NEW DEPENDENT FUNCTION")
    return list(set(missing_definition_list))


def identify_missing_macros(function_node, source_file, target_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_function_list, missing_macro_list
    Output.normal("\tidentifying missing macros")
    ref_list = extract_reference_node_list(function_node)
    dec_list = extract_decl_list(function_node)
    function_identifier = function_node['identifier']
    for ref_node in ref_list:
        node_type = str(ref_node['type'])
        if node_type == "Macro":
            identifier = str(ref_node['value'])
            node_child_count = len(ref_node['children'])
            if function_identifier in identifier or "(" in identifier:
                continue
            if identifier in Common.STANDARD_MACRO_LIST:
                continue
            if node_child_count:
                for child_node in ref_node['children']:
                    identifier = str(child_node['value'])
                    if identifier in Common.STANDARD_MACRO_LIST:
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
    ast_node = Generator.get_ast_json(source_path)
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
    function_list = generate_candidate_function_list(estimated_loc, var_expr_map)
    stack_info = Tracer.stack_c

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
