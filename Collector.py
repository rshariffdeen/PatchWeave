#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
import Output
import Logger


def collect_symbolic_expressions(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tcollecting symbolic expressions")
    var_expr_map = dict()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            for line in trace_file:
                if '[var-expr]' in line:
                    line = line.replace("[var-expr] ", "")
                    var_name, var_expr = line.split(":")
                    var_expr_map[var_name] = var_expr.replace("\n", "")
    return var_expr_map


def collect_symbolic_path(file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting symbolic path conditions")
    constraints = dict()
    if os.path.exists(file_path):
        source_path = ""
        path_condition = ""
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:condition]' in line:
                    if project_path in line:
                        source_path = str(line.replace("[path:condition]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        source_path = os.path.abspath(source_path)
                        path_condition = str(line.replace("[path:condition]", '')).split(" : ")[1]
                        continue
                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        constraints[source_path] = path_condition
                        source_path = ""
                        path_condition = ""
    return constraints

