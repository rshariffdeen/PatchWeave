#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import Logger
import Generator
import Converter
import Finder
import Extractor


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
        node_value_a, discard_list = Converter.get_member_expr_str(node_a)
        node_value_b, discard_list = Converter.get_member_expr_str(node_b)
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


def is_function_important(source_path, function_call_node, sym_path_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ast_tree = Generator.get_ast_json(source_path)
    function_ref_node = function_call_node['children'][0]
    function_name = function_ref_node['value']
    function_def_node = Finder.search_function_node_by_name(ast_tree, function_name)
    function_node, file_path = Extractor.extract_complete_function_node(function_def_node, source_path)
    file_path = os.path.abspath(file_path)
    start_line = function_node['start line']
    end_line = function_node['end line']
    line_numbers = set(range(int(start_line), int(end_line) + 1))
    for line_number in line_numbers:
        loc_id = file_path + ":" + str(line_number)
        if loc_id in sym_path_list:
            return True
    return False
