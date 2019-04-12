#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import execute_command, get_file_extension_list, error_exit
from ast import ASTGenerator
import Mapper
import Logger
import Filter
import Emitter


def merge_var_info(var_expr_map, var_value_map):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_info = dict()
    # print(var_expr_map)
    # print(var_value_map)
    for var_name in var_value_map:
        if var_name in var_expr_map:
            info = dict()
            # print(var_name)
            info["data_type"] = var_expr_map[var_name]['data_type']
            # print(info["data_type"])
            info["value_list"] = var_value_map[var_name]['value_list']
            # print(info["value_list"])
            info["expr_list"] = var_expr_map[var_name]['expr_list']
            var_info[var_name] = info
    # print(var_info)
    return var_info


def merge_var_map(map_a, map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_map = dict()
    for var_name in map_a:
        if var_name in map_b:
            error_exit("unhandled exception in merging var maps")
        else:
            var_map[var_name] = map_a[var_name]

    for var_name in map_b:
        if var_name not in map_a:
            var_map[var_name] = map_b[var_name]

    # print(var_info)
    return var_map


def merge_macro_info(info_a, info_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    macro_info = dict()
    for macro_name in info_a:
        info = info_a[macro_name]
        if macro_name in info_b.keys():
            error_exit("MULTIPLE USAGE OF MACRO")
        macro_info[macro_name] = info

    for macro_name in info_b:
        info = info_b[macro_name]
        macro_info[macro_name] = info
    return macro_info


def merge_header_info(info_a, info_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    header_info = dict()
    for header_name in info_a:
        info = info_a[header_name]
        if header_name in info_b.keys():
            error_exit("MULTIPLE USAGE OF HEADER")
        header_info[header_name] = info

    for header_name in info_b:
        info = info_b[header_name]
        header_info[header_name] = info
    return header_info
