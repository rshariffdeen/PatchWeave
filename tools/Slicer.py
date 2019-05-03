#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import get_code, error_exit
from ast import ASTGenerator
import Extractor
import Oracle
import Logger
import Filter
import Emitter


def slice_code_from_trace(diff_info, trace_list, path_a, path_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    # print(diff_info)
    for diff_loc in diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(path_a, path_b)
        skip_lines = list()
        diff_loc_info = diff_info[diff_loc]
        # print(diff_loc)
        if 'new-lines' in diff_loc_info.keys():
            start_line, end_line = diff_loc_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            # print(line_numbers)
            for line_number in line_numbers:
                # print(line_number)
                loc_id = source_file + ":" + str(line_number)
                if loc_id not in trace_list:
                    if Oracle.is_declaration_line(source_file, line_number):
                        skip_lines.append(line_number)
                    statement = get_code(source_file, line_number)
                    # print(statement)
                    # if "if" in statement:
                    #     continue
                    if "}" in statement:
                        continue
                    if "{" in statement:
                        continue
                    skip_lines.append(line_number)
                    # print(skip_lines)
        diff_loc_info['skip-lines'] = skip_lines
        diff_info[diff_loc] = diff_loc_info
    # print(diff_info)
    return diff_info


def slice_skipped_diff_locs(diff_info):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_diff_info = dict()
    for diff_loc in diff_info:
        diff_loc_info = diff_info[diff_loc]
        if 'new-lines' in diff_loc_info.keys():
            start_line, end_line = diff_loc_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            skip_lines = diff_loc_info['skip-lines']
            if set(line_numbers) == set(skip_lines):
                continue
        ast_script = diff_loc_info['ast-script']
        if not ast_script:
            continue
        filtered_diff_info[diff_loc] = diff_loc_info
    if not filtered_diff_info:
        error_exit("no AST changes to be transplanted")
    return filtered_diff_info


def slice_ast_script(diff_info, project_path_a, project_path_b, trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_diff_info = dict()
    for diff_loc in diff_info:
        diff_loc_info = diff_info[diff_loc]
        # print(diff_loc)
        # print(diff_loc_info)
        Emitter.special("\t" + diff_loc)
        skip_lines = diff_loc_info['skip-lines']
        # print(skip_lines)
        ast_script = diff_loc_info['ast-script']
        # print(ast_script)
        source_path_a, line_number_a = diff_loc.split(":")
        source_path_b = str(source_path_a).replace(project_path_a,
                                                   project_path_b)
        try:
            ast_map_a = ASTGenerator.get_ast_json(source_path_a)
            ast_map_b = ASTGenerator.get_ast_json(source_path_b)
        except:
            continue
        filtered_ast_script = Filter.filter_ast_script_by_skip_line(ast_script,
                                                                    ast_map_a,
                                                                    ast_map_b,
                                                                    skip_lines
                                                                    )
        # print(filtered_ast_script)
        filtered_ast_script = Filter.filter_ast_script_by_node_type(filtered_ast_script,
                                                                    ast_map_a,
                                                                    ast_map_b,
                                                                    trace_list,
                                                                    source_path_b
                                                                    )
        # print(filtered_ast_script)
        diff_loc_info['ast-script'] = filtered_ast_script
        filtered_diff_info[diff_loc] = diff_loc_info
        # print(filtered_ast_script)
    return filtered_diff_info


def slice_function_calls(diff_info, sym_path_list, path_a, path_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for diff_loc in diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(path_a, path_b)
        diff_loc_info = diff_info[diff_loc]
        skip_lines = diff_loc_info['skip-lines']
        if 'new-lines' in diff_loc_info.keys():
            function_call_node_list = Extractor.extract_function_call_list(source_file,
                                                                           start_line)
            start_line, end_line = diff_loc_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            for line_number in line_numbers:
                loc_id = source_file + ":" + str(line_number)
                if line_number in function_call_node_list.keys():
                    # print(loc_id)
                    # print(skip_lines)
                    if not Oracle.is_function_important(source_file,
                                                        function_call_node_list[line_number],
                                                        sym_path_list
                                                        ):
                        skip_lines.append(line_number)
                    # print(skip_lines)
        diff_loc_info['skip-lines'] = skip_lines
        diff_info[diff_loc] = diff_loc_info
    return diff_info


def slice_redundant_patches(diff_info, suspicious_locs):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_diff_info = dict()
    inserted_similar_loc_list = list()
    for diff_loc in diff_info:
        source_path, start_line = diff_loc.split(":")
        source_file = source_path.split("/")[-1]
        patch_loc = source_file + ":" + start_line
        if patch_loc in suspicious_locs.keys():
            bug_reason = suspicious_locs[patch_loc]
            # print(patch_loc)
            similar_loc_list = list()
            for suspicious_loc in suspicious_locs:
                if suspicious_locs[suspicious_loc] == bug_reason:
                    similar_loc_list.append(suspicious_loc)
            # print(similar_loc_list)
            redundant = False
            for similar_loc in similar_loc_list:
                if similar_loc in inserted_similar_loc_list:
                    redundant = True
                    break
            # print(redundant)
            if not redundant:
                filtered_diff_info[diff_loc] = diff_info[diff_loc]
                inserted_similar_loc_list.append(patch_loc)
        else:
            filtered_diff_info[diff_loc] = diff_info[diff_loc]
    return filtered_diff_info
