#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import execute_command, get_file_extension_list, error_exit
from ast import ASTGenerator
import Mapper
import Logger
import Filter
import Emitter


def merge_var_info(var_expr, var_value):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_info = dict()
    for var_name in var_value:
        info = dict()
        info["data_type"] = var_value[var_name]['data_type']
        info["value_list"] = var_value[var_name]['value_list']
        info["expr_list"] = var_expr[var_name]['expr_list']
        var_info[var_name] = info
    return var_info


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
