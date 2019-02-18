#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
from common.Utilities import execute_command, backup_file, show_partial_diff, get_code
from common import Definitions
import phases.Concolic
from ast import ASTGenerator
import phases.Analyse
import phases.Trace
from tools import Mapper, Identifier, Generator, Logger, Solver, Collector, Emitter, Writer, Finder

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

FILE_VAR_EXPR_LOG_A = ""
FILE_VAR_EXPR_LOG_B = ""
FILE_VAR_EXPR_LOG_C = ""
FILE_VAR_MAP = ""
FILE_SKIP_LIST = ""
FILE_AST_SCRIPT = ""
FILE_TEMP_FIX = ""

FILENAME_BACKUP = "temp-source"


def get_sym_path(source_location):
    sym_path = ""
    if Definitions.VALUE_PATH_A in source_location:
        for path in phases.Trace.list_trace_a:
            if path in phases.Concolic.sym_path_a.keys():
                sym_path = phases.Concolic.sym_path_a[path]
            if path == source_location:
                break
    elif Definitions.VALUE_PATH_B in source_location:
        for path in phases.Trace.list_trace_b:
            if path in phases.Concolic.sym_path_b.keys():
                sym_path = phases.Concolic.sym_path_b[path]
            if path == source_location:
                break
    elif Definitions.VALUE_PATH_C in source_location:
        for path in phases.Trace.list_trace_c:
            if path in phases.Concolic.sym_path_c.keys():
                sym_path = phases.Concolic.sym_path_c[path]
            if path == source_location:
                break
    return sym_path


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


def execute_ast_transformation(source_path_b, source_path_d):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global modified_source_list
    Emitter.normal("\t\texecuting AST transformation")
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


def weave_headers(header_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for header_name in header_list:
        Emitter.normal(header_name)
        target_file = missing_header_list[header_name]
        transplant_code = "\n#include<" + header_name + ">\n"
        def_insert_line = Finder.find_definition_insertion_point(target_file)
        backup_file(target_file, FILENAME_BACKUP)
        insert_patch(transplant_code, target_file, def_insert_line)
        backup_file_path = Definitions.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, target_file)


def weave_macros():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.sub_title("transplanting missing macros")
    for macro_name in missing_macro_list:
        Emitter.normal(macro_name)
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
        backup_file_path = Definitions.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, target_file)


def weave_functions():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global def_insert_point, missing_header_list
    Emitter.sub_title("transplanting missing functions")
    for function_name in missing_function_list:
        info = missing_function_list[function_name]
        node_id = info['node_id']
        source_path_b = info['source_b']
        source_path_d = info['source_d']
        Emitter.normal(function_name)
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
        backup_file_path = Definitions.DIRECTORY_BACKUP + "/" + FILENAME_BACKUP
        show_partial_diff(backup_file_path, source_path_d)


def weave_code(diff_loc, diff_loc_info, path_a, path_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    operation = diff_loc_info['operation']
    ast_script = diff_loc_info['ast-script']
    source_path_a, line_number_a = diff_loc.split(":")
    source_path_b = str(source_path_a).replace(path_a, path_b)
    byte_list = Solver.compute_common_bytes(diff_loc)
    estimate_loc = Identifier.identify_divergent_point(byte_list)

    if operation == 'insert':
        start_line_b, end_line_b = diff_loc_info['new-lines']
        skip_line_list = diff_loc_info['skip-lines']
        Writer.write_skip_list(skip_line_list, FILE_SKIP_LIST)
        line_range_b = (start_line_b, end_line_b)
        line_range_a = (-1, -1)
        Generator.generate_symbolic_expressions(source_path_b,
                                                start_line_b,
                                                end_line_b,
                                                FILE_VAR_EXPR_LOG_B)

        var_expr_map_b = Collector.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_B)
        # print(var_expr_map_b)
        insertion_loc_list = Identifier.identify_insertion_points(estimate_loc, var_expr_map_b)
        # print(insertion_loc_list)
        ast_script_c = list()
        for insertion_loc in insertion_loc_list:
            Emitter.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            ast_map_c = ASTGenerator.get_ast_json(source_path_c)
            source_path_d = source_path_c.replace(Definitions.Project_C.path, Definitions.Project_D.path)
            function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
            position_c = get_ast_node_position(function_node, int(line_number_c))
            for script_line in ast_script:
                inserting_node_str = script_line.split(" into ")[0]
                inserting_node_id = int((inserting_node_str.split("(")[1]).split(")")[0])
                inserting_node = get_ast_node_by_id(ast_map_b, inserting_node_id)
                translated_command = inserting_node_str + " into " + position_c + "\n"
                identify_missing_functions(inserting_node, source_path_b, source_path_d, skip_line_list)
                # identify_missing_macros(inserting_node, source_path_b, source_path_d)
                ast_script_c.append(translated_command)
            Mapper.generate_symbolic_expressions(source_path_c, line_number_c, line_number_c, FILE_VAR_EXPR_LOG_C, False)
            var_expr_map_c = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_C)
            # print(var_expr_map_b)
            # print(var_expr_map_c)
            var_map = Mapper.generate_mapping(var_expr_map_b, var_expr_map_c)
            # print(var_map)
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
        Mapper.generate_symbolic_expressions(source_path_b, line_range_b[0], line_range_b[1], FILE_VAR_EXPR_LOG_B)
        var_expr_map_b = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_B)
        # print(var_expr_map_b)
        Mapper.generate_symbolic_expressions(source_path_a, line_range_a[0], line_range_a[1], FILE_VAR_EXPR_LOG_A)
        var_expr_map_a = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_A)
        # print(var_expr_map_a)
        insertion_loc_list = identify_insertion_points(estimate_loc, var_expr_map_a)
        # print(insertion_loc_list)
        ast_script_c = list()
        for insertion_loc in insertion_loc_list:
            Emitter.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            source_path_d = source_path_c.replace(Definitions.Project_C.path, Definitions.Project_D.path)
            ast_map_c = ASTGenerator.get_ast_json(source_path_c)
            # print(insertion_loc)
            function_node = get_fun_node(ast_map_c, int(line_number_c), source_path_c)
            position_c = get_ast_node_position(function_node, int(line_number_c))
            Mapper.generate_symbolic_expressions(source_path_c, line_number_c, line_number_c, FILE_VAR_EXPR_LOG_C, False)
            var_expr_map_c = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG_C)
            # print(var_expr_map_c)
            var_map_ac = Mapper.generate_mapping(var_expr_map_a, var_expr_map_c)
            var_map_bc = Mapper.generate_mapping(var_expr_map_b, var_expr_map_c)
            for script_line in ast_script:
                translated_command = script_line
                if "Insert" in script_line:
                    inserting_node_str = script_line.split(" into ")[0]
                    inserting_node_id = int((inserting_node_str.split("(")[1]).split(")")[0])
                    inserting_node = get_ast_node_by_id(ast_map_b, inserting_node_id)
                    translated_command = inserting_node_str + " into " + position_c
                    identify_missing_functions(inserting_node, source_path_b, source_path_d, skip_line_list)
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

