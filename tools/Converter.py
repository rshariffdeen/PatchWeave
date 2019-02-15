#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
sys.path.append('./ast/')
from common.Utilities import error_exit, execute_command
import Logger
from common import Definitions

SYMBOLIC_CONVERTER = "gen-bout"
BINARY_CONVERTER = "extract-bc"


def convert_cast_expr(ast_node, only_string=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = ""
    var_list = list()
    type_node = ast_node['children'][0]
    type_value = type_node['value']
    param_node = ast_node['children'][1]
    param_node_type = param_node['type']
    if param_node_type == "MemberExpr":
        param_node_var_name, param_node_aux_list = convert_member_expr(param_node)
        var_list = var_list + param_node_aux_list
        var_name = "(" + type_value + ") " + param_node_var_name + " " + var_name
    else:
        error_exit("Unhandled CStyleCAST")
    if only_string:
        return var_name
    return var_name, var_list


def convert_member_expr(ast_node, only_string=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    var_name = ""
    if 'value' in ast_node.keys():
        node_value = ast_node['value']
        var_name = str(node_value.split(":")[-1])
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
            if iterating_var_type == "DeclRefExpr":
                iterating_var_ref_type = iterating_var_node['ref_type']
                if iterating_var_ref_type in ["VarDecl", "ParmVarDecl"]:
                    var_list.append(iterating_var_name)
                    if var_name[:2] == "->":
                        var_name = "." + var_name[2:]
                    var_name = "[" + iterating_var_name + "]" + var_name
        elif child_node_type == "ParenExpr":
            param_node = child_node['children'][0]
            param_node_type = param_node['type']
            param_node_var_name = ""
            param_node_aux_list = list()
            if param_node_type == "MemberExpr":
                param_node_var_name, param_node_aux_list = convert_member_expr(param_node)
            elif param_node_type == "CStyleCastExpr":
                param_node_var_name, param_node_aux_list = convert_cast_expr(param_node)
            var_list = var_list + param_node_aux_list
            var_name = "(" + param_node_var_name + ")" + var_name
            break
        elif child_node_type == "CStyleCastExpr":
            cast_var_name, cast_node_aux_list = convert_cast_expr(child_node)
            var_list = var_list + cast_node_aux_list
            var_name = cast_var_name + var_name
            break
        elif child_node_type == "MemberExpr":
            child_node_value = child_node['value']
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
        return var_name
    return var_name, var_list


def convert_poc_to_ktest(file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    concrete_file = open(Definitions.VALUE_PATH_POC, 'rb')
    bit_size = os.fstat(concrete_file.fileno()).st_size
    convert_command = SYMBOLIC_CONVERTER + " --sym-file " + Definitions.VALUE_PATH_POC
    execute_command(convert_command)
    move_command = "mv file.bout " + file_path
    execute_command(move_command)
    return bit_size


def convert_binary_to_llvm(binary_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
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

