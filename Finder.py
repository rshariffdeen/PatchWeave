#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import Logger
import Oracle


def search_matching_node(ast_node, search_node, var_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_id = int(ast_node['id'])
    node_type = str(ast_node['type'])
    search_node_type = str(search_node['type'])
    if node_type == search_node_type:
        if Oracle.is_node_equal(ast_node, search_node, var_map):
            return node_type + "(" + str(node_id) + ")"

    for child_node in ast_node['children']:
        if len(child_node['children']) > 0:
            target_node_str = search_matching_node(child_node, search_node, var_map)
            if target_node_str is not None:
                return target_node_str


def find_ast_node_position(ast_node, line_number):
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
            return find_ast_node_position(prev_child_node, line_number)
        prev_child_node = child_node
        child_index += 1
    return find_ast_node_position(prev_child_node, line_number)


def search_ast_node_by_id(ast_node, find_id):
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
            return search_ast_node_by_id(prev_child_node, int(find_id))
        else:
            prev_child_node = child_node
    return search_ast_node_by_id(prev_child_node, int(find_id))


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

