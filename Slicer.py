#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, get_code
import Output
import Common
import Generator
import Vector
import Logger
import Differ
import Concolic
import Tracer
import Weaver


def is_function_important(source_path, function_call_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ast_tree = Generator.get_ast_json(source_path)
    function_ref_node = function_call_node['children'][0]
    function_name = function_ref_node['value']
    function_node_id = Weaver.get_function_node_id(ast_tree, function_name)
    function_def_node = Weaver.get_ast_node_by_id(ast_tree, int(function_node_id))
    function_node, file_path = Weaver.get_complete_function_node(function_def_node, source_path)
    file_path = os.path.abspath(file_path)
    start_line = function_node['start line']
    end_line = function_node['end line']
    line_numbers = set(range(int(start_line), int(end_line) + 1))
    for line_number in line_numbers:
        loc_id = file_path + ":" + str(line_number)
        if loc_id in Concolic.sym_path_b.keys():
            return True
    return False


def get_function_call_lines(source_file, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    line_list = dict()
    ast_tree = Generator.get_ast_json(source_file)
    function_node = Weaver.get_fun_node(ast_tree, int(line_number), source_file)
    call_node_list = Weaver.extract_function_calls(function_node)
    for call_node in call_node_list:
        line_list[call_node['start line']] = call_node
    return line_list


def get_declaration_lines(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    line_list = list()
    child_count = len(ast_node['children'])
    node_start_line = int(ast_node['start line'])
    node_end_line = int(ast_node['end line'])
    start_column = int(ast_node['start column'])
    end_column = int(ast_node['end column'])
    node_type = ast_node['type']

    if node_type in ["VarDecl"]:
        line_list.append(node_start_line)
        return line_list

    if child_count:
        for child_node in ast_node['children']:
            line_list = line_list + list(set(get_declaration_lines(child_node)))
    return list(set(line_list))


def is_declaration_line(source_file, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ast_tree = Generator.get_ast_json(source_file)
    function_node = Weaver.get_fun_node(ast_tree, int(line_number), source_file)
    if function_node is None:
        error_exit("FUNCTION NODE NOT FOUND!!")
    dec_line_list = get_declaration_lines(function_node)
    if line_number in dec_line_list:
        return True
    return False


def filter_from_trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("slicing unrelated diff based on trace")
    for diff_loc in Differ.diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
        skip_lines = list()
        diff_info = Differ.diff_info[diff_loc]
        if 'new-lines' in diff_info.keys():
            start_line, end_line = diff_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            for line_number in line_numbers:
                loc_id = source_file + ":" + str(line_number)
                if loc_id not in Tracer.list_trace_b:
                    if is_declaration_line(source_file, line_number):
                        continue
                    statement = get_code(source_file, line_number)

                    if "}" not in statement:
                        skip_lines.append(line_number)
        diff_info['skip-lines'] = skip_lines



def filter_function_calls():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("slicing unrelated function calls")
    for diff_loc in Differ.diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
        diff_info = Differ.diff_info[diff_loc]
        skip_lines = diff_info['skip-lines']
        if 'new-lines' in diff_info.keys():
            function_call_list = get_function_call_lines(source_file, start_line)
            start_line, end_line = diff_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            for line_number in line_numbers:
                loc_id = source_file + ":" + str(line_number)
                if line_number in function_call_list.keys():
                    if not is_function_important(source_file, function_call_list[line_number]):
                        skip_lines.append(line_number)
        diff_info['skip-lines'] = skip_lines


def slice_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filter_from_trace()
    filter_function_calls()


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title("starting " + title + "...")
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


def slice():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Slicing unrelated code")
    safe_exec(slice_diff, "removing unwanted code")
