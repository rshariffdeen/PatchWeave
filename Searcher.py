#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, get_file_list, restore_file, extract_bitcode, reset_git, is_intersect
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Output
import Common
import Logger
import Concolic
import Generator
import Builder
import Weaver
import collections
import Differ
import Mapper
import z3



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


def search_function_node_by_name(ast_node, function_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    function_id = -1
    for child_node in ast_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "FunctionDecl":
            child_node_identifier = child_node['identifier']
            if child_node_identifier == function_name:
                function_id = int(child_node['id'])
    return function_id


def is_function_important(source_path, function_call_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ast_tree = Generator.get_ast_json(source_path)
    function_ref_node = function_call_node['children'][0]
    function_name = function_ref_node['value']
    function_node_id = get_function_node_id(ast_tree, function_name)
    function_def_node = get_ast_node_by_id(ast_tree, int(function_node_id))
    function_node, file_path = get_complete_function_node(function_def_node, source_path)
    file_path = os.path.abspath(file_path)
    start_line = function_node['start line']
    end_line = function_node['end line']
    line_numbers = set(range(int(start_line), int(end_line) + 1))
    for line_number in line_numbers:
        loc_id = file_path + ":" + str(line_number)
        if loc_id in Concolic.sym_path_b.keys():
            return True
    return False


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


def get_function_call_lines(source_file, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    line_list = dict()
    ast_tree = Generator.get_ast_json(source_file)
    function_node = Weaver.get_fun_node(ast_tree, int(line_number), source_file)
    if function_node is None:
        return line_list
    call_node_list = Weaver.extract_function_calls(function_node)
    for call_node in call_node_list:
        line_list[call_node['start line']] = call_node
    return line_list
