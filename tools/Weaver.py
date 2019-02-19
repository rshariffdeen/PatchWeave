#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
from common.Utilities import execute_command, backup_file, show_partial_diff, get_code
from common import Definitions, Values
import phases.Concolic
from ast import ASTGenerator
from phases import Trace
import Mapper
import Identifier
import Generator
import Logger
import Collector
import Emitter
import Writer
import Finder
import Extractor


TOOL_AST_PATCH = "patchweave"
FILE_TEMP_FIX = Definitions.DIRECTORY_TMP + "/temp-fix"
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


def execute_ast_transformation(source_path_b, source_path_d, file_info):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global modified_source_list
    skip_file, ast_script_file,var_map_file = file_info
    Emitter.normal("\t\texecuting AST transformation")
    parameters = " -map=" + var_map_file + " -script=" + ast_script_file
    parameters += " -source=" + source_path_b + " -target=" + source_path_d
    parameters += " -skip-list=" + skip_file
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


def weave_functions(missing_function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    def_insert_point = ""
    missing_header_list = dict()
    missing_macro_list = dict()

    for function_name in missing_function_list:
        info = missing_function_list[function_name]
        node_id = info['node_id']
        source_path_b = info['source_b']
        source_path_d = info['source_d']
        Emitter.normal(function_name)
        ast_map_b = ASTGenerator.get_ast_json(source_path_b)
        function_def_node = Finder.search_ast_node_by_id(ast_map_b, int(node_id))
        function_node, function_source_file = Extractor.extract_complete_function_node(function_def_node,
                                                                                       source_path_b)
        missing_def_list = Identifier.identify_missing_definitions(function_node)
        def_insert_point = Finder.find_definition_insertion_point(source_path_d)

        Identifier.identify_missing_macros(function_node, function_source_file, source_path_d)
        Identifier.identify_missing_headers(function_node, source_path_d)
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

    return missing_header_list


def weave_code(diff_loc, diff_loc_info, path_a, path_b, path_c, path_d,
               bit_size, sym_poc_path,
               file_info, trace_list, estimate_loc):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    out_file_info, log_file_info = file_info
    skip_list_file, ast_script_file, var_map_file = out_file_info
    var_log_a, var_log_b, var_log_c = log_file_info
    operation = diff_loc_info['operation']
    ast_script = diff_loc_info['ast-script']
    source_path_a, line_number_a = diff_loc.split(":")
    source_path_b = str(source_path_a).replace(path_a, path_b)
    missing_function_list = dict()

    if operation == 'insert':
        start_line_b, end_line_b = diff_loc_info['new-lines']
        skip_line_list = diff_loc_info['skip-lines']
        Writer.write_skip_list(skip_line_list, skip_list_file)
        line_range_b = (start_line_b, end_line_b)
        line_range_a = (-1, -1)

        Emitter.sub_sub_title("computing symbolic expressions for Donor")
        Generator.generate_symbolic_expressions(source_path_b,
                                                start_line_b,
                                                end_line_b,
                                                bit_size,
                                                sym_poc_path,
                                                var_log_b
                                                )

        var_expr_map_b = Collector.collect_symbolic_expressions(var_log_b)
        # print(var_expr_map_b)
        insertion_loc_list = Identifier.identify_insertion_points(estimate_loc,
                                                                  var_expr_map_b,
                                                                  bit_size,
                                                                  sym_poc_path,
                                                                  trace_list,
                                                                  var_log_c
                                                                  )

        ast_script_c = list()
        Emitter.sub_sub_title("generating patch for insertion point")
        ast_map_a = ASTGenerator.get_ast_json(source_path_a)
        ast_map_b = ASTGenerator.get_ast_json(source_path_b)

        for insertion_loc in insertion_loc_list:
            Emitter.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            ast_map_c = ASTGenerator.get_ast_json(source_path_c)
            source_path_d = source_path_c.replace(path_c, path_d)
            function_node = Finder.search_function_node_by_loc(ast_map_c,
                                                               int(line_number_c),
                                                               source_path_c)

            position_c = Finder.find_ast_node_position(function_node,
                                                       int(line_number_c))
            Emitter.normal("\t\t\tgenerating AST script")
            for script_line in ast_script:
                inserting_node_str = script_line.split(" into ")[0]
                inserting_node_id = int((inserting_node_str.split("(")[1]).split(")")[0])
                inserting_node = Finder.search_ast_node_by_id(ast_map_b,
                                                              inserting_node_id)
                translated_command = inserting_node_str + " into " + position_c + "\n"
                missing_function_list = Identifier.identify_missing_functions(ast_map_c,
                                                      inserting_node,
                                                      source_path_b,
                                                      source_path_d,
                                                      skip_line_list)

                # Identifier.identify_missing_macros(inserting_node,
                #                                    source_path_b,
                #                                    source_path_d)
                ast_script_c.append(translated_command)
            Writer.write_ast_script(ast_map_c, ast_script_file)
            Emitter.sub_sub_title("computing symbolic expressions for target")
            Generator.generate_symbolic_expressions(source_path_c,
                                                    line_number_c,
                                                    line_number_c,
                                                    bit_size,
                                                    sym_poc_path,
                                                    var_log_c,
                                                    False
                                                    )

            var_expr_map_c = Collector.collect_symbolic_expressions(var_log_c)
            # print(var_expr_map_b)
            # print(var_expr_map_c)
            Emitter.sub_sub_title("generating variable mapping from donor to target")
            var_map = Mapper.map_variable(var_expr_map_b, var_expr_map_c)
            for var_a in var_map:
                Emitter.special("\t\t\t " + var_a + " -> " + var_map[var_a])
            # print(var_map)
            # print(ast_script_c)
            Writer.write_var_map(var_map, var_map_file)
            ret_code = execute_ast_transformation(source_path_b,
                                                  source_path_d,
                                                  out_file_info)
            if ret_code == 0:
                break
    elif operation == 'modify':
        start_line_a, end_line_a = diff_loc_info['old-lines']
        start_line_b, end_line_b = diff_loc_info['new-lines']
        skip_line_list = diff_loc_info['skip-lines']
        Writer.write_skip_list(skip_line_list, skip_list_file)
        line_range_a = (start_line_a, end_line_a)
        line_range_b = (start_line_b, end_line_b)

        Generator.generate_symbolic_expressions(source_path_b,
                                                start_line_b,
                                                end_line_b,
                                                bit_size,
                                                sym_poc_path,
                                                var_log_b)
        var_expr_map_b = Collector.collect_symbolic_expressions(var_log_b)
        # print(var_expr_map_b)

        Generator.generate_symbolic_expressions(source_path_a,
                                                start_line_a,
                                                end_line_a,
                                                bit_size,
                                                sym_poc_path,
                                                var_log_a)

        var_expr_map_a = Collector.collect_symbolic_expressions(var_log_a)
        # print(var_expr_map_a)
        insertion_loc_list = Identifier.identify_insertion_points(estimate_loc,
                                                                  var_expr_map_a,
                                                                  bit_size,
                                                                  sym_poc_path,
                                                                  trace_list,
                                                                  var_log_a
                                                                  )

        exit(1)
        # print(insertion_loc_list)
        ast_script_c = list()
        for insertion_loc in insertion_loc_list:
            Emitter.normal("\t\t" + insertion_loc)
            source_path_c, line_number_c = insertion_loc.split(":")
            source_path_d = source_path_c.replace(path_c, path_d)
            ast_map_c = ASTGenerator.get_ast_json(source_path_c)
            # print(insertion_loc)
            function_node = Finder.search_function_node_by_loc(ast_map_c,
                                                               int(line_number_c),
                                                               source_path_c)

            position_c = Finder.find_ast_node_position(function_node,
                                                       int(line_number_c))



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
    return missing_function_list
