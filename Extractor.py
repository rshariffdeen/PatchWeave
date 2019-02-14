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


def extract_complete_function_node(function_def_node, source_path):
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


def extract_child_id_list(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    id_list = list()
    for child_node in ast_node['children']:
        child_id = int(child_node['id'])
        id_list.append(child_id)
        grand_child_list = extract_child_id_list(child_node)
        if grand_child_list:
            id_list = id_list + grand_child_list
    if id_list:
        id_list = list(set(id_list))
    return id_list


def extract_function_call_lines(source_file, line_number):
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
