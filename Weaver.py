#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, backup_file, show_partial_diff, get_file_list, get_code
import Output
import Common
import Logger
import Concolic
import Generator
import Differ
import Tracer
import Mapper
import Fixer

function_list_a = list()
function_list_b = list()
function_list_c = list()
target_candidate_function_list = list()
mapping_ba = dict()
missing_function_list = dict()
missing_macro_list = dict()
missing_header_list = dict()

modified_source_list = list()

var_expr_map_a = dict()
var_expr_map_b = dict()
var_expr_map_c = dict()

ast_map_a = dict()
ast_map_b = dict()
ast_map_c = dict()

TOOL_AST_PATCH = "patchweave"

FILE_VAR_EXPR_LOG_A = Common.DIRECTORY_OUTPUT + "/log-sym-expr-a"
FILE_VAR_EXPR_LOG_B = Common.DIRECTORY_OUTPUT + "/log-sym-expr-b"
FILE_VAR_EXPR_LOG_C = Common.DIRECTORY_OUTPUT + "/log-sym-expr-c"
FILE_VAR_MAP = Common.DIRECTORY_OUTPUT + "/var-map"
FILE_SKIP_LIST = Common.DIRECTORY_OUTPUT + "/skip-list"
FILE_AST_SCRIPT = Common.DIRECTORY_OUTPUT + "/gen-ast-script"
FILE_TEMP_FIX = Common.DIRECTORY_OUTPUT + "/temp-fix"
FILE_MACRO_DEF = Common.DIRECTORY_OUTPUT + "/macro-def"
FILENAME_BACKUP = "temp-source"


def extract_source_list(trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tcollecting source file list from trace ...")
    source_list = list()
    for trace_line in trace_list:
        source_path, line_number = str(trace_line).split(":")
        source_path = source_path.strip()
        if source_path not in source_list:
            source_list.append(source_path)
    return source_list


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
        model = Mapper.get_model_from_solver(sym_path)
        bytes_temp = Mapper.extract_values_from_model(model)
        count = len(list(set(byte_list).intersection(bytes_temp.keys())))
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

    # print("\t\testimated loc:\n\t\t" + str(estimated_loc))
    # filtered_list = list()
    # for i in range(n, length):
    #     if list_trace_c[i] not in filtered_list:
    #         filtered_list.append(list_trace_c[i])
    # for path in filtered_list:
    #     print(path)
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
        model_a = Mapper.get_model_from_solver(div_sympath)
        bytes_a = Mapper.extract_values_from_model(model_a)
        model_c = Mapper.get_model_from_solver(last_sympath_c)
        bytes_c = Mapper.extract_values_from_model(model_c)
        common_byte_list = list(set(bytes_a.keys()).intersection(bytes_c.keys()))
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


def get_fun_node(ast_node, line_number, source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    file_name = source_path.split("/")[-1]
    for child_node in ast_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "FunctionDecl":
            if "file" in child_node.keys():
                function_source = child_node['file']
                if file_name not in function_source:
                    continue
            child_node_start_line = int(child_node['start line'])
            child_node_end_line = int(child_node['end line'])
            if line_number in range(child_node_start_line, child_node_end_line + 1):
                return child_node
    return None


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


def is_node_equal(node_a, node_b, var_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_type_a = str(node_a['type'])
    node_type_b = str(node_b['type'])
    if node_type_a != node_type_b:
        return False

    if node_type_a in ["DeclStmt", "DeclRefExpr", "VarDecl"]:
        node_value_a = node_a['value']
        node_value_b = node_b['value']
        if node_value_a == node_value_b or node_value_a == var_map[node_value_b] or \
                node_value_b == var_map[node_value_a]:
            return True
        else:
            return False
    elif node_type_a == "MemberExpr":
        node_value_a, discard_list = Mapper.get_member_expr_str(node_a)
        node_value_b, discard_list = Mapper.get_member_expr_str(node_b)
        if node_value_a == node_value_b:
            return True
        else:
            if node_value_b in var_map and node_value_a == var_map[node_value_b]:
                return True
            else:
                return False

    elif node_type_a == "BinaryOperator":
        left_child_a = node_a['children'][0]
        right_child_a = node_a['children'][1]
        left_child_b = node_b['children'][0]
        right_child_b = node_b['children'][1]
        if is_node_equal(left_child_a, left_child_b, var_map) and \
                is_node_equal(right_child_a, right_child_b, var_map):
            return True
        else:
            return False


def get_matching_node(ast_node, search_node, var_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_id = int(ast_node['id'])
    node_type = str(ast_node['type'])
    search_node_type = str(search_node['type'])
    if node_type == search_node_type:
        if is_node_equal(ast_node, search_node, var_map):
            return node_type + "(" + str(node_id) + ")"

    for child_node in ast_node['children']:
        if len(child_node['children']) > 0:
            target_node_str = get_matching_node(child_node, search_node, var_map)
            if target_node_str is not None:
                return target_node_str


def get_ast_node_position(ast_node, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_id = ast_node['id']
    node_type = ast_node['type']
    child_index = 0
    line_number = int(line_number)
    prev_child_node = ""
    for child_node in ast_node['children']:
        child_node_id = int(child_node['id'])
        child_node_type = str(child_node['type'])
        child_node_start_line = int(child_node['start line'])
        child_node_end_line = int(child_node['end line'])
        if child_node_start_line == line_number:
            return str(node_type) + "(" + str(node_id) + ") at " + str(child_index)
        elif child_node_start_line > line_number:
            return get_ast_node_position(prev_child_node, line_number)
        prev_child_node = child_node
        child_index += 1
    return get_ast_node_position(prev_child_node, line_number)


def get_child_id_list(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    id_list = list()
    for child_node in ast_node['children']:
        child_id = int(child_node['id'])
        id_list.append(child_id)
        grand_child_list = get_child_id_list(child_node)
        if grand_child_list:
            id_list = id_list + grand_child_list
    if id_list:
        id_list = list(set(id_list))
    return id_list


def merge_ast_script(ast_script, ast_node_a, ast_node_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    merged_ast_script = list()
    inserted_node_list = list()
    deleted_node_list = list()
    for script_line in ast_script:
        if "Insert" in script_line:
            node_id_1 = int(((script_line.split(" into ")[0]).split("(")[1]).split(")")[0])
            node_id_2 = int(((script_line.split(" into ")[1]).split("(")[1]).split(")")[0])
            if node_id_2 not in inserted_node_list:
                merged_ast_script.append(script_line)
            inserted_node_list.append(node_id_1)
        elif "Delete" in script_line:
            node_id = int((script_line.split("(")[1]).split(")")[0])
            if node_id in deleted_node_list:
                continue
            node = get_ast_node_by_id(ast_node_a, node_id)
            child_id_list = get_child_id_list(node)
            deleted_node_list = deleted_node_list + child_id_list
            merged_ast_script.append(script_line)
        elif "Move" in script_line:
            move_position = int((script_line.split(" at ")[1]))
            move_node_str = (script_line.split(" into ")[0]).replace("Move ", "")
            move_node_id = int((move_node_str.split("(")[1]).split(")")[0])
            target_node_id_b = int(((script_line.split(" into ")[1]).split("(")[1]).split(")")[0])
            target_node_id_a = mapping_ba[target_node_id_b]
            target_node_a = get_ast_node_by_id(ast_node_a, target_node_id_a)
            replacing_node = target_node_a['children'][move_position]
            replacing_node_id = replacing_node['id']
            replacing_node_str = replacing_node['type'] + "(" + str(replacing_node['id']) + ")"
            script_line = "Replace " + replacing_node_str + " with " + move_node_str

            merged_ast_script.append(script_line)
            deleted_node_list.append(replacing_node_id)
            child_id_list = get_child_id_list(replacing_node)
            deleted_node_list = deleted_node_list + child_id_list

    return merged_ast_script


def filter_ast_script(ast_script, line_range_a, line_range_b, ast_node_a, ast_node_b, skip_lines):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_ast_script = list()
    line_range_start_a, line_range_end_a = line_range_a
    line_range_start_b, line_range_end_b = line_range_b
    line_numbers_a = set(range(int(line_range_start_a), int(line_range_end_a) + 1))
    line_numbers_b = set(range(int(line_range_start_b), int(line_range_end_b) + 1))
    merged_ast_script = merge_ast_script(ast_script, ast_node_a, ast_node_b)
    for script_line in merged_ast_script:
        if "Insert" in script_line:
            node_id_b = int(((script_line.split(" into ")[0]).split("(")[1]).split(")")[0])
            node_b = get_ast_node_by_id(ast_node_b, node_id_b)
            node_line_start = int(node_b['start line'])
            node_line_end = int(node_b['end line']) + 1
            if node_line_start in skip_lines:
                continue
            node_line_numbers = set(range(node_line_start, node_line_end))
            intersection = line_numbers_b.intersection(node_line_numbers)
            if intersection:
                filtered_ast_script.append(script_line)
        elif "Delete" in script_line:
            node_id_a = int((script_line.split("(")[1]).split(")")[0])
            node_a = get_ast_node_by_id(ast_node_a, node_id_a)
            node_line_start = int(node_a['start line'])
            node_line_end = int(node_a['end line']) + 1
            node_line_numbers = set(range(node_line_start, node_line_end))
            intersection = line_numbers_a.intersection(node_line_numbers)
            if intersection:
                filtered_ast_script.append(script_line)
        elif "Replace" in script_line:
            node_id_a = int(((script_line.split(" with ")[0]).split("(")[1]).split(")")[0])
            node_a = get_ast_node_by_id(ast_node_a, node_id_a)
            node_line_start = int(node_a['start line'])
            node_line_end = int(node_a['end line']) + 1
            node_line_numbers = set(range(node_line_start, node_line_end))
            intersection = line_numbers_a.intersection(node_line_numbers)
            if intersection:
                filtered_ast_script.append(script_line)
    return filtered_ast_script


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


def execute_ast_transformation(source_path_b, source_path_d):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global modified_source_list
    Output.normal("\t\texecuting AST transformation")
    parameters = " -map=" + FILE_VAR_MAP + " -script=" + FILE_AST_SCRIPT
    parameters += " -source=" + source_path_b + " -target=" + source_path_d
    parameters += " -skip-list=" + FILE_SKIP_LIST
    transform_command = TOOL_AST_PATCH + parameters + " > " + FILE_TEMP_FIX
    ret_code = int(execute_command(transform_command))
    if source_path_d not in modified_source_list:
        modified_source_list.append(source_path_d)
    if ret_code == 0:
        move_command = "cp " + FILE_TEMP_FIX + " " + source_path_d
        show_partial_diff(source_path_d, FILE_TEMP_FIX)
        execute_command(move_command)
    return ret_code


def show_final_patch(source_path_a, source_path_b, source_path_c, source_path_d):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())


def extract_function_calls(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    call_expr_list = list()
    node_type = str(ast_node["type"])
    if node_type == "CallExpr":
        call_expr_list.append(ast_node)
    else:
        if len(ast_node['children']) > 0:
            for child_node in ast_node['children']:
                child_call_list = extract_function_calls(child_node)
                call_expr_list = call_expr_list + child_call_list
    return call_expr_list


def extract_reference_node_list(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ref_node_list = list()
    node_type = str(ast_node["type"])
    if node_type in ["Macro", "DeclRefExpr"]:
        ref_node_list.append(ast_node)
    else:
        if len(ast_node['children']) > 0:
            for child_node in ast_node['children']:
                child_ref_list = extract_reference_node_list(child_node)
                ref_node_list = ref_node_list + child_ref_list
    return ref_node_list


def extract_decl_list(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    dec_list = list()
    node_type = str(ast_node["type"])
    if node_type in ["FunctionDecl", "VarDecl", "ParmVarDecl"]:
        identifier = str(ast_node['identifier'])
        dec_list.append(identifier)

    if len(ast_node['children']) > 0:
        for child_node in ast_node['children']:
            child_dec_list = extract_decl_list(child_node)
            dec_list = dec_list + child_dec_list
    return list(set(dec_list))


# def is_definition_exist(ast_node, definition):
#     Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
#     print("def=" + definition)
#     if definition in ["true", "false"]:
#         return True
#     for child_node in ast_node['children']:
#         child_node_type = child_node['type']
#         if child_node_type in ["VarDecl", "ParmVarDecl"]:
#             child_node_identifier = child_node['identifier']
#             print(child_node_identifier)
#             if child_node_identifier == definition:
#                 return True
#     return False


def get_function_node_id(ast_node, function_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    function_id = -1
    for child_node in ast_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "FunctionDecl":
            child_node_identifier = child_node['identifier']
            if child_node_identifier == function_name:
                function_id = int(child_node['id'])
    return function_id


def identify_missing_functions(ast_node, source_path_b, source_path_d):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tidentifying missing function calls")
    global missing_function_list
    call_list = extract_function_calls(ast_node)
    for call_expr in call_list:
        function_ref_node = call_expr['children'][0]
        function_name = function_ref_node['value']
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


def extract_macro_definitions(source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting macro definitions from\n\t\t" + str(source_path))
    extract_command = "clang -E -dM " + source_path + " > " + FILE_MACRO_DEF
    execute_command(extract_command)
    with open(FILE_MACRO_DEF, "r") as macro_file:
        macro_def_list = macro_file.readlines()
        return macro_def_list


def transplant_missing_header():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.sub_title("transplanting missing header")
    global missing_header_list
    for header_name in missing_header_list:
        Output.normal(header_name)
        target_file = missing_header_list[header_name]
        transplant_code = "\n#include<" + header_name + ">\n"
        def_insert_line = get_definition_insertion_point(target_file)
        backup_file(target_file, FILENAME_BACKUP)
        insert_patch(transplant_code, target_file, def_insert_line)
        backup_file_path = Common.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, target_file)


def transplant_missing_macros():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.sub_title("transplanting missing macros")
    for macro_name in missing_macro_list:
        Output.normal(macro_name)
        macro_info = missing_macro_list[macro_name]
        source_file = macro_info['source']
        target_file = macro_info['target']
        macro_def_list = extract_macro_definitions(source_file)
        def_insert_line = get_definition_insertion_point(target_file)
        transplant_code = ""
        for macro_def in macro_def_list:
            if macro_name in macro_def:
                if "#define" in macro_def:
                    if macro_name in macro_def.split(" "):
                        transplant_code += "\n" + macro_def + "\n"
        backup_file(target_file, FILENAME_BACKUP)
        insert_patch(transplant_code, target_file, def_insert_line)
        backup_file_path = Common.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, target_file)


def get_complete_function_node(function_def_node, source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    source_dir = "/".join(source_path.split("/")[:-1])
    if len(function_def_node['children']) > 1:
        source_file_loc = source_dir + "/" + function_def_node['file']
        source_file_loc = os.path.abspath(source_file_loc)
        return function_def_node, source_file_loc
    else:
        header_file_loc = source_dir + "/" + function_def_node['file']
        function_name = function_def_node['identifier']
        source_file_loc = header_file_loc.replace(".h", ".c")
        source_file_loc = os.path.abspath(source_file_loc)
        if not os.path.exists(source_file_loc):
            source_file_name = source_file_loc.split("/")[-1]
            header_file_dir = "/".join(source_file_loc.split("/")[:-1])
            search_dir = os.path.dirname(header_file_dir)
            while not os.path.exists(source_file_loc):
                search_dir_file_list = get_file_list(search_dir)
                for file_name in search_dir_file_list:
                    if source_file_name in file_name and file_name[-2:] == ".c":
                        source_file_loc = file_name
                        break
                search_dir = os.path.dirname(search_dir)
        ast_tree = Generator.get_ast_json(source_file_loc)
        function_node_id = get_function_node_id(ast_tree, function_name)
        function_node = get_ast_node_by_id(ast_tree, function_node_id)
        return function_node, source_file_loc


def transplant_missing_functions():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global def_insert_point, missing_header_list
    Output.sub_title("transplanting missing functions")
    for function_name in missing_function_list:
        info = missing_function_list[function_name]
        node_id = info['node_id']
        source_path_b = info['source_b']
        source_path_d = info['source_d']
        Output.normal(function_name)
        function_def_node = get_ast_node_by_id(ast_map_a, int(node_id))
        function_node, function_source_file = get_complete_function_node(function_def_node, source_path_b)
        missing_def_list = identify_missing_definitions(function_node)
        def_insert_point = get_definition_insertion_point(source_path_d)
        identify_missing_macros(function_node, function_source_file, source_path_d)
        identify_missing_headers(function_node, source_path_d)
        start_line = function_node["start line"]
        end_line = function_node["end line"]
        # print(function_name)
        original_function = ""
        for i in range(int(start_line), int(end_line + 1)):
            original_function += get_code(function_source_file, int(i)) + "\n"
        # translated_patch = translate_patch(original_patch, var_map_ac)
        backup_file(source_path_d, FILENAME_BACKUP)
        insert_patch(original_function, source_path_d, def_insert_point)
        backup_file_path = Common.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, source_path_d)


def transplant_code(diff_info, diff_loc):
    global mapping_ba, var_expr_map_a, var_expr_map_b, var_expr_map_c
    global ast_map_a, ast_map_b, ast_map_c
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    byte_list = compute_common_bytes(diff_loc)
    estimate_loc = estimate_divergent_point(byte_list)
    operation = diff_info['operation']
    source_path_a, line_number_a = diff_loc.split(":")
    source_path_b = str(source_path_a).replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
    ast_script = Differ.get_ast_script(source_path_a, source_path_b)
    ast_map_a = Generator.get_ast_json(source_path_a)
    ast_map_b = Generator.get_ast_json(source_path_b)
    mapping_ba = Differ.get_ast_mapping(source_path_a, source_path_b)

    if operation == 'insert':
        start_line_b, end_line_b = diff_info['new-lines']
        skip_line_list = diff_info['skip-lines']
        output_skip_list(skip_line_list)
        line_range_b = (start_line_b, end_line_b)
        line_range_a = (-1, -1)
        filtered_ast_script = filter_ast_script(ast_script, line_range_a, line_range_b, ast_map_a, ast_map_b, skip_line_list)
        Mapper.generate_symbolic_expressions(source_path_b, start_line_b,  end_line_b, FILE_VAR_EXPR_LOG_B)
        var_expr_map_b = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_B)
        # print(var_expr_map_b)
        insertion_loc_list = identify_insertion_points(estimate_loc, var_expr_map_b)
        # print(insertion_loc_list)
        ast_script_c = list()
        for insertion_loc in insertion_loc_list:
            Output.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            ast_map_c = Generator.get_ast_json(source_path_c)
            source_path_d = source_path_c.replace(Common.Project_C.path, Common.Project_D.path)
            function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
            position_c = get_ast_node_position(function_node, int(line_number_c))
            for script_line in filtered_ast_script:
                inserting_node_str = script_line.split(" into ")[0]
                inserting_node_id = int((inserting_node_str.split("(")[1]).split(")")[0])
                inserting_node = get_ast_node_by_id(ast_map_b, inserting_node_id)
                translated_command = inserting_node_str + " into " + position_c + "\n"
                identify_missing_functions(inserting_node, source_path_b, source_path_d)
                # identify_missing_macros(inserting_node, source_path_b, source_path_d)
                ast_script_c.append(translated_command)
            Mapper.generate_symbolic_expressions(source_path_c, line_number_c, line_number_c, FILE_VAR_EXPR_LOG_C, False)
            var_expr_map_c = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_C)
            # print(var_expr_map_b)
            # print(var_expr_map_c)
            var_map = Mapper.generate_mapping(var_expr_map_b, var_expr_map_c)
            print(var_map)
            # print(ast_script_c)

            output_var_map(var_map)
            output_ast_script(ast_script_c)
            ret_code = execute_ast_transformation(source_path_b, source_path_d)
            if ret_code == 0:
                break
    elif operation == 'modify':
        line_range_a = diff_info['old-lines']
        line_range_b = diff_info['new-lines']
        skip_line_list = diff_info['skip-lines']
        output_skip_list(skip_line_list)
        filtered_ast_script = filter_ast_script(ast_script, line_range_a, line_range_b, ast_map_a, ast_map_b, skip_line_list)
        Mapper.generate_symbolic_expressions(source_path_b, line_range_b[0], line_range_b[1], FILE_VAR_EXPR_LOG_B)
        var_expr_map_b = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_B)
        # print(var_expr_map_b)
        Mapper.generate_symbolic_expressions(source_path_a, line_range_a[0], line_range_a[1], FILE_VAR_EXPR_LOG_A)
        var_expr_map_a = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_A)
        # print(var_expr_map_b)
        insertion_loc_list = identify_insertion_points(estimate_loc, var_expr_map_a)
        # print(insertion_loc_list)
        ast_script_c = list()
        for insertion_loc in insertion_loc_list:
            Output.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            source_path_d = source_path_c.replace(Common.Project_C.path, Common.Project_D.path)
            ast_map_c = Generator.get_ast_json(source_path_c)
            # print(insertion_loc)
            function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
            position_c = get_ast_node_position(function_node, int(line_number_c))
            Mapper.generate_symbolic_expressions(source_path_c, line_number_c, line_number_c, FILE_VAR_EXPR_LOG_C, False)
            var_expr_map_c = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_C)
            # print(var_expr_map_c)
            var_map_ac = Mapper.generate_mapping(var_expr_map_a, var_expr_map_c)
            var_map_bc = Mapper.generate_mapping(var_expr_map_b, var_expr_map_c)
            for script_line in filtered_ast_script:
                translated_command = script_line
                if "Insert" in script_line:
                    inserting_node_str = script_line.split(" into ")[0]
                    inserting_node_id = int((inserting_node_str.split("(")[1]).split(")")[0])
                    inserting_node = get_ast_node_by_id(ast_map_b, inserting_node_id)
                    translated_command = inserting_node_str + " into " + position_c
                    identify_missing_functions(inserting_node, source_path_b, source_path_d)
                    # identify_missing_macros(inserting_node, source_path_b, source_path_d)
                    ast_script_c.append(translated_command)
                elif "Replace" in script_line:
                    replacing_node_str = (script_line.split(" with ")[0]).replace("Replace ", "")
                    replacing_node_id = (replacing_node_str.split("(")[1]).split(")")[0]
                    replacing_node = get_ast_node_by_id(ast_map_a, int(replacing_node_id))
                    target_node_str = get_matching_node(function_node, replacing_node, var_map_ac)
                    if target_node_str is None:
                        continue
                    elif "Macro" in target_node_str:
                        print("insdie macro")
                        target_node_id = int((target_node_str.split("(")[1]).split(")")[0])
                        target_node = get_ast_node_by_id(ast_map_c, target_node_id)
                        ast_script_c.append(translated_command)
                        start_line = target_node["start line"]
                        end_line = target_node["end line"]
                        original_patch = ""
                        for i in range(int(start_line), int(end_line + 1)):
                            original_patch += get_code(source_path_b, int(i)) + "\n"
                            print(original_patch)
                        translated_patch = translate_patch(original_patch, var_map_ac)
                        print(translated_patch)
                        insert_patch(translated_patch, source_path_c, line_number_c)
                    else:
                        translated_command = script_line.replace(replacing_node_str, target_node_str)
                        ast_script_c.append(translated_command)
            # print(var_map_ac)
            output_var_map(var_map_ac)
            output_ast_script(ast_script_c)
            ret_code = execute_ast_transformation(source_path_b, source_path_d)
            if ret_code == 0:
                break


def transplant_patch():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for diff_loc in Differ.diff_info.keys():
        Output.normal(diff_loc)
        diff_info = Differ.diff_info[diff_loc]
        transplant_code(diff_info, diff_loc)
    transplant_missing_functions()
    transplant_missing_macros()
    transplant_missing_header()
    Fixer.check()


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


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title( title + "...")
    description = title[0].lower() + title[1:]
    try:
        Logger.information("running " + str(function_def))
        if not args:
            result = function_def()
        else:
            result = function_def(*args)
        duration = str(time.time() - start_time)
        Output.success("\n\tSuccessful " + description + ", after " + duration + " seconds.")
    except Exception as exception:
        duration = str(time.time() - start_time)
        Output.error("Crash during " + description + ", after " + duration + " seconds.")
        error_exit(exception, "Unexpected error during " + description + ".")
    return result


def weave():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("repairing bug")
    safe_exec(transplant_patch, "transplanting patch")
