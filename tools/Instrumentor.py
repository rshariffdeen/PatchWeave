#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
from common.Utilities import execute_command, error_exit
import Emitter
import Logger
import collections
import Finder
import Extractor
import Oracle
from common import Values
from ast import ASTGenerator


def instrument_klee_var_expr(source_path, start_line, end_line, stack_info, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\t\tinstrumenting source code")
    is_error_on_exit = True
    orig_variable_list = Extractor.extract_variable_list(source_path, start_line, end_line, only_in_range)
    # print(orig_variable_list)
    insert_code = dict()
    instrument_code = ""

    for variable, line_number in orig_variable_list:
        if line_number in insert_code.keys():
            insert_code[
                line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
        else:
            insert_code[
                line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"

    sorted_insert_code = collections.OrderedDict(sorted(insert_code.items(), reverse=True))

    ast_map = ASTGenerator.get_ast_json(source_path)
    function_node = Finder.search_function_node_by_loc(ast_map, start_line, source_path)
    function_name = function_node['identifier']

    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            for insert_line in sorted_insert_code:
                instrument_code = sorted_insert_code[insert_line]
                if Values.PATH_B not in source_path:
                    if Oracle.is_loc_on_stack(source_path, function_name, insert_line, stack_info):
                        instrument_code += "exit(1);\n"
                        is_error_on_exit = False
                existing_line = content[insert_line-1]
                content[insert_line-1] = existing_line + instrument_code

    with open(source_path, 'w') as source_file:
        source_file.writelines(content)

    ret_code = 1
    while ret_code != 0:
        syntax_fix_command = "clang-tidy --fix-errors " + source_path
        # print(syntax_fix_command)
        execute_command(syntax_fix_command)
        syntax_check_command = "clang-tidy " + source_path
        # print(syntax_check_command)
        ret_code = int(execute_command(syntax_check_command))

    return is_error_on_exit
