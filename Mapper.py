#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
import Output
import Common
import Logger
import Concolic
import Generator
import Tracer


var_expr_map_a = dict()
var_expr_map_b = dict()
var_expr_map_c = dict()


def collect_symbolic_expressions(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting symbolic expressions")
    var_expr_map = dict()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            for line in trace_file:
                if '[var-expr]' in line:
                    line = line.replace("[var-expr] ", "")
                    var_name, var_expr = line.split(":")
                    var_expr_map[var_name] = var_expr
    return var_expr_map


def generate_symbolic_expressions(source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating symbolic expressions")
