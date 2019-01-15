#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
import Output
import Common
import Logger
import Concolic
import Generator
import Differ
import Tracer
import Mapper

function_list_a = list()
function_list_b = list()
function_list_c = list()
target_candidate_function_list = list()
filtered_trace_list = list()
mapping_ba = dict()

FILE_VAR_EXPR_LOG = Common.DIRECTORY_OUTPUT + "/log-sym-expr"


def extract_source_list(trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting source file list from trace ...")
    source_list = list()
    for trace_line in trace_list:
        source_path, line_number = str(trace_line).split(":")
        source_path = source_path.strip()
        if source_path not in source_list:
            source_list.append(source_path)
    return source_list


def get_function_map(source_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting function list from source files ...")
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


def extract_trace_function_list(source_list, trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting function list from trace ...")
    trace_function_list = list()
    source_function_map = get_function_map(source_list)
    unique_trace_list = list(set(trace_list))
    source_line_map = dict()
    for trace_line in unique_trace_list:
        source_path, line_number = str(trace_line).split(":")
        if source_path not in source_line_map.keys():
            source_line_map[source_path] = list()
        source_line_map[source_path].append(int(line_number))

    for source_path in source_line_map:
        function_list = source_function_map[source_path]
        trace_line_list = source_line_map[source_path]
        for line_number in trace_line_list:
            for function_name, begin_line, finish_line in function_list:
                if line_number in range(begin_line, finish_line):
                    trace_function = source_path + ":" + function_name
                    trace_function += ":" + str(begin_line) + ":" + str(finish_line)
                    if trace_function not in trace_function_list:
                        trace_function_list.append(trace_function)
    return trace_function_list


def generate_candidate_function_list(estimate_loc):
    global filtered_trace_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating candidate functions")
    trace_list = Concolic.list_trace_c
    length = len(trace_list)
    filtered_trace_list = list()
    for n in range (length-1, 0, -1):
        filtered_trace_list.append(trace_list[n])
        if estimate_loc is trace_list[n]:
            break
    filtered_trace_list.reverse()
    source_list_c = extract_source_list(filtered_trace_list)
    candidate_list = extract_trace_function_list(source_list_c, filtered_trace_list)
    return candidate_list


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
    length = len(Concolic.list_trace_c) - 1

    for n in range(length, 0, -1):
        path = Concolic.list_trace_c[n]
        if path in candidate_list:
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
        for path in Concolic.list_trace_a:
            if path in Concolic.sym_path_a.keys():
                sym_path = Concolic.sym_path_a[path]
            if path is source_location:
                break
    elif Common.VALUE_PATH_B in source_location:
        for path in Concolic.list_trace_b:
            if path in Concolic.sym_path_b.keys():
                sym_path = Concolic.sym_path_b[path]
            if path is source_location:
                break
    elif Common.VALUE_PATH_C in source_location:
        for path in Concolic.list_trace_c:
            if path in Concolic.sym_path_c.keys():
                sym_path = Concolic.sym_path_c[path]
            if path is source_location:
                break
    return sym_path


def compute_common_bytes(div_source_loc):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tanalysing common bytes in symbolic paths")
    div_sympath = get_sym_path(div_source_loc)
    last_sympath_c = Concolic.sym_path_c[Concolic.sym_path_c.keys()[-1]]
    model_a = Mapper.get_model_from_solver(div_sympath)
    bytes_a = Mapper.extract_values_from_model(model_a)
    model_c = Mapper.get_model_from_solver(last_sympath_c)
    bytes_c = Mapper.extract_values_from_model(model_c)
    return list(set(bytes_a.keys()).intersection(bytes_c.keys()))


def get_code(source_path, line_number):
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            return content[line_number-1]
    return None


def translate_patch(patch_code, var_map):
    for var in var_map.keys():
        if var in patch_code:
            str(patch_code).replace(var, var_map[var])
    return patch_code


def insert_patch(patch_code, source_path, line_number):
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            content[line_number] = patch_code

    with open(source_path, 'w') as source_file:
        source_file.writelines(content)


def get_fun_node(ast_node, line_number, source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    file_name = source_path.split("/")[-1]
    for child_node in ast_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "FunctionDecl":
            function_source = child_node['file']
            if file_name in function_source:
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


def get_ast_node_position(ast_node, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_id = ast_node['id']
    node_type = ast_node['type']
    child_index = 0
    line_number = int(line_number)
    prev_child_node = ""
    for child_node in ast_node['children']:
        child_node_start_line = int(child_node['start line'])
        child_node_end_line = int(child_node['end line'])
        if child_node_start_line == line_number:
            return str(node_type) + "(" + str(node_id) + ") at " + str(child_index)
        elif child_node_start_line > line_number:
            return get_ast_node_position(prev_child_node, line_number)
        prev_child_node = child_node
        child_index += 1
    return get_ast_node_position(prev_child_node, line_number)


def get_ast_node_list(ast_map, line_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    line_start, line_end = line_range
    node_list = list()

    for line_number in range(line_start, line_end + 1):
        func_node = get_fun_node(ast_map, line_number)

    return node_list


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


def merge_ast_script(ast_script, ast_node):
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
            node = get_ast_node_by_id(ast_node, node_id)
            child_id_list = get_child_id_list(node)
            deleted_node_list = deleted_node_list + child_id_list
            merged_ast_script.append(script_line)
    return merged_ast_script


def filter_ast_script(ast_script, line_range, ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_ast_script = list()
    line_range_start, line_range_end = line_range
    line_numbers = set(range(int(line_range_start), int(line_range_end) + 1))
    merged_ast_script = merge_ast_script(ast_script, ast_node)
    for script_line in merged_ast_script:
        if "Insert" in script_line:
            node_id_b = int(((script_line.split(" into ")[0]).split("(")[1]).split(")")[0])
            node_b = get_ast_node_by_id(ast_node, node_id_b)
            node_line_start = int(node_b['start line'])
            node_line_end = int(node_b['end line']) + 1
            node_line_numbers = set(range(node_line_start, node_line_end))
            intersection = line_numbers.intersection(node_line_numbers)
            if intersection:
                filtered_ast_script.append(script_line)
        elif "Delete" in script_line:
            node_id_a = int((script_line.split("(")[1]).split(")")[0])
            node_a = get_ast_node_by_id(ast_node, node_id_a)
            node_line_start = int(node_a['start line'])
            node_line_end = int(node_a['end line']) + 1
            node_line_numbers = set(range(node_line_start, node_line_end))
            intersection = line_numbers.intersection(node_line_numbers)
            if intersection:
                filtered_ast_script.append(script_line)
    return filtered_ast_script


def transplant_code():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global mapping_ba
    partitioned_diff = dict()
    # for diff_loc in Differ.diff_info.keys():
    #     source_path_a, line_number_a = diff_loc.split(":")
    #     if source_path_a not in partitioned_diff.keys():
    #         partitioned_diff[source_path_a] = dict()
    #     partitioned_diff[source_path_a][line_number_a] = Differ.diff_info[diff_loc]
    #
    # for source_path_a in partitioned_diff:
    #
    #     source_path_b = str(source_path_a).replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
    #     ast_script = Differ.get_ast_script(source_path_a, source_path_b)
    #     ast_map_a = Generator.generate_json(source_path_a)
    #     ast_map_b = Generator.generate_json(source_path_b)

    for diff_loc in Differ.diff_info.keys():
        Output.normal(diff_loc)
        byte_list = compute_common_bytes(diff_loc)
        estimate_loc = estimate_divergent_point(byte_list)
        diff_info = Differ.diff_info[diff_loc]
        operation = diff_info['operation']
        source_path_a, line_number_a = diff_loc.split(":")
        source_path_b = str(source_path_a).replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
        ast_script = Differ.get_ast_script(source_path_a, source_path_b)
        ast_map_a = Generator.get_ast_json(source_path_a)
        ast_map_b = Generator.get_ast_json(source_path_b)
        mapping_ba = Differ.get_ast_mapping(source_path_a, source_path_b)
        if operation == 'insert':
            start_line_b, end_line_b = diff_info['new-lines']
            filtered_ast_script = filter_ast_script(ast_script, (start_line_b, end_line_b), ast_map_b)
            insertion_loc_list = identify_insertion_points(estimate_loc)
            ast_script_c = list()
            for insertion_loc in insertion_loc_list:
                Output.normal("\t\t" + insertion_loc)
                source_path_c, line_number_c = insertion_loc.split(":")
                ast_map_c = Generator.get_ast_json(source_path_c)
                print(insertion_loc)
                function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
                position_c = get_ast_node_position(function_node, int(line_number_c))
                for script_line in filtered_ast_script:
                    inserting_node = script_line.split(" into ")[0]
                    translated_command = inserting_node + " into " + position_c
                    ast_script_c.append(translated_command)
        elif operation == 'modify':
            start_line_b, end_line_b = diff_info['new-lines']
            start_line_a, end_line_a = diff_info['old-lines']
            filtered_ast_script_b = filter_ast_script(ast_script, (start_line_b, end_line_b), ast_map_b)

            filtered_ast_script_a = filter_ast_script(ast_script, (start_line_a, end_line_a), ast_map_a)
            print(filtered_ast_script_a)
            exit()
            insertion_loc_list = identify_insertion_points(estimate_loc)
            ast_script_c = list()
            for insertion_loc in insertion_loc_list:
                Output.normal("\t\t" + insertion_loc)
                source_path_c, line_number_c = insertion_loc.split(":")
                ast_map_c = Generator.get_ast_json(source_path_c)
                print(insertion_loc)
                function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
                position_c = get_ast_node_position(function_node, int(line_number_c))
                for script_line in filtered_ast_script:
                    inserting_node = script_line.split(" into ")[0]
                    translated_command = inserting_node + " into " + position_c
                    ast_script_c.append(translated_command)

        else:
            continue

        for insertion_loc in insertion_loc_list:
            Output.normal("\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            Mapper.generate_symbolic_expressions(source_path_c, line_number_c)
            sym_expr_map = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG)
            var_map = Mapper.generate_mapping(Mapper.var_expr_map_a, sym_expr_map)

            if operation == 'insert':

                ast_map_b = Generator.generate_json(source_path_b)
                start_line, end_line = diff_info['new-lines']
                original_patch = ""
                for i in range(int(start_line), int(end_line + 1)):
                    original_patch += get_code(source_path_b, int(i)) + "\n"
                print(original_patch)
                translated_patch = translate_patch(original_patch, var_map)
                print(translated_patch)
                insert_patch(translated_patch, source_path_c, line_number_c)

            elif operation == 'delete':
                original_patch = get_code(source_path_a, int(line_number_a))


def get_function_range_from_trace(function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    stack_info = Tracer.stack_c
    range_map = dict()

    for func in function_list:
        source_path, function_name, start_line, end_line = func.split(":")
        function_def = source_path + ":" + function_name
        if function_def not in range_map.keys():
            range_map[function_def] = dict()

        start_line = int(start_line)
        end_line = int(end_line)
        trace_start_line = end_line
        trace_end_line = start_line

        for trace_line in filtered_trace_list:
            if source_path in trace_line:
                line_number = int(trace_line.split(":")[1])
                if line_number in range(start_line, end_line+1):
                    if line_number < trace_start_line:
                        trace_start_line = line_number

                    if trace_end_line < line_number:
                        trace_end_line = line_number

        range_map[function_def]['start'] = int(trace_start_line)
        range_map[function_def]['end'] = int(trace_end_line)

        # if source_path in stack_info.keys():
        #     if function_name in stack_info[source_path].keys():
        #         range_map[function_def]['end'] = int(stack_info[source_path][function_name])

    # print(range_map)
    return range_map


def identify_insertion_points(estimated_loc):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    insertion_point_list = list()
    function_list = generate_candidate_function_list(estimated_loc)
    stack_info = Tracer.stack_c
    range_map = get_function_range_from_trace(function_list)

    for function_def in range_map:
        start_line = int(range_map[function_def]['start'])
        end_line = int(range_map[function_def]['end'])
        for n in range(start_line, end_line + 1):
            source_path = function_def.split(":")[0]
            insertion_point_list.append(source_path + ":" + str(n))
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
    Output.title("transplanting patch")
    safe_exec(transplant_code, "transplanting code")
