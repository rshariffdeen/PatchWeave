#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
from common.Utilities import error_exit, execute_command
import Logger


SYMBOLIC_CONVERTER = "gen-bout"
BINARY_CONVERTER = "extract-bc"


def convert_cast_expr(ast_node, only_string=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = ""
    var_list = list()
    type_node = ast_node['children'][0]
    type_value = type_node['value']
    data_type = str(type_node['data_type'])
    param_node = ast_node['children'][1]
    param_node_type = param_node['type']
    if param_node_type == "MemberExpr":
        param_node_var_name, param_node_data_type, param_node_aux_list = convert_member_expr(param_node)
        var_list = var_list + param_node_aux_list
        var_name = "(" + type_value + ") " + param_node_var_name + " " + var_name
    else:
        error_exit("Unhandled CStyleCAST")
    if only_string:
        return var_name, data_type
    return var_name, var_list


def convert_array_iterator(iterator_node):
    iterator_node_type = str(iterator_node['type'])
    var_list = list()
    if iterator_node_type in ["VarDecl", "ParmVarDecl"]:
        iterator_name = str(iterator_node['value'])
        iterator_data_type = str(iterator_node['data_type'])
        var_list.append((iterator_name, iterator_data_type))
        var_name = "[" + iterator_name + "]"
    elif iterator_node_type == "DeclRefExpr":
        iterator_name = str(iterator_node['value'])
        iterator_data_type = str(iterator_node['data_type'])
        var_list.append((iterator_name, iterator_data_type))
        var_name = "[" + iterator_name + "]"
    elif iterator_node_type in ["IntegerLiteral"]:
        iterator_value = str(iterator_node['value'])
        var_name = "[" + iterator_value + "]"
    else:
        print(iterator_node)
        error_exit("Unknown iterator type for array_subscript")
    return var_name, var_list


def convert_array_subscript(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    var_name = ""
    var_data_type = ""
    array_node = ast_node['children'][0]
    array_name = str(array_node['value'])
    array_type = str(array_node['type'])
    array_data_type = str(array_node['data_type'])
    var_data_type = array_data_type.split("[")[0]
    if array_type == "DeclRefExpr":
        iterator_node = ast_node['children'][1]
        iterator_node_type = str(iterator_node['type'])
        var_name, var_list = convert_array_iterator(iterator_node)
        var_name = array_name + var_name
    elif array_type == "MemberExpr":
        iterator_node = ast_node['children'][1]
        array_name, array_data_type = convert_member_expr(array_node, True)
        var_name, var_list = convert_array_iterator(iterator_node)
        var_name = array_name + var_name
    else:
        print(array_type)
        print(array_node)
        print(ast_node)
        error_exit("Unknown data type for array_subscript")
    return var_name, var_data_type, var_list


def convert_member_expr(ast_node, only_string=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    var_name = ""
    var_data_type = ""
    if 'value' in ast_node.keys():
        node_value = ast_node['value']
        var_name = str(node_value.split(":")[-1])
        var_data_type = str(ast_node['data_type'])
        if "union" in node_value:
            var_name = "." + var_name
        else:
            var_name = "->" + var_name
    child_node = ast_node['children'][0]
    while child_node:
        child_node_type = child_node['type']
        if child_node_type == "DeclRefExpr":
            var_name = str(child_node['value']) + var_name
        elif child_node_type == "ArraySubscriptExpr":
            iterating_var_node = child_node['children'][1]
            iterating_var_name = iterating_var_node['value']
            iterating_var_type = iterating_var_node['type']
            iterating_var_data_type = iterating_var_node['data_type']
            if var_data_type == "":
                var_data_type = iterating_var_data_type
            if iterating_var_type == "DeclRefExpr":
                iterating_var_ref_type = iterating_var_node['ref_type']
                if iterating_var_ref_type in ["VarDecl", "ParmVarDecl"]:
                    var_list.append((iterating_var_name, iterating_var_data_type))
                    if var_name[:2] == "->":
                        var_name = "." + var_name[2:]
                    var_name = "[" + iterating_var_name + "]" + var_name
        elif child_node_type == "ParenExpr":
            param_node = child_node['children'][0]
            param_node_type = param_node['type']
            param_node_var_name = ""
            param_node_aux_list = list()
            if param_node_type == "MemberExpr":
                param_node_var_name, var_data_type, param_node_aux_list = convert_member_expr(param_node)
            elif param_node_type == "CStyleCastExpr":
                param_node_var_name, var_data_type, param_node_aux_list = convert_cast_expr(param_node)
            var_list = var_list + param_node_aux_list
            var_name = "(" + param_node_var_name + ")" + var_name
            break
        elif child_node_type == "CStyleCastExpr":
            cast_var_name, var_data_type, cast_node_aux_list = convert_cast_expr(child_node)
            var_list = var_list + cast_node_aux_list
            var_name = cast_var_name + var_name
            break
        elif child_node_type == "MemberExpr":
            child_node_value = child_node['value']
            var_data_type = str(child_node['data_type'])
            if "union" in child_node_value:
                var_name = "." + str(child_node_value.split(":")[-1]) + var_name
            else:
                var_name = "->" + str(child_node_value.split(":")[-1]) + var_name
        else:
            print(ast_node)
            error_exit("unhandled exception at membership expr -> str")
        if len(child_node['children']) > 0:
            child_node = child_node['children'][0]
        else:
            child_node = None
    if only_string:
        return var_name, var_data_type
    return var_name, var_data_type, var_list


def convert_poc_to_ktest(poc_path, ktest_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    concrete_file = open(poc_path, 'rb')
    bit_size = os.fstat(concrete_file.fileno()).st_size
    convert_command = SYMBOLIC_CONVERTER + " --sym-file " + poc_path
    execute_command(convert_command)
    move_command = "mv file.bout " + ktest_path
    execute_command(move_command)
    return bit_size


def convert_binary_to_llvm(binary_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    remove_command = "rm " + binary_path + ".bc"
    # print(remove_command)
    execute_command(remove_command)
    extract_command = BINARY_CONVERTER + " " + binary_path
    # print(extract_command)
    execute_command(extract_command)
    return binary_directory, binary_name


def convert_node_to_str(ast_node):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    node_str = ""
    node_type = str(ast_node['type'])
    if node_type in ["DeclStmt", "DeclRefExpr", "VarDecl"]:
        node_str = str(ast_node['value'])
    if str(ast_node['type']) == "BinaryOperator":
        operator = str(ast_node['value'])
        right_operand = convert_node_to_str(ast_node['children'][1])
        left_operand = convert_node_to_str(ast_node['children'][0])
        return left_operand + " " + operator + " " + right_operand
    return node_str

