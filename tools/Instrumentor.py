#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
from common.Utilities import execute_command, error_exit
import Emitter
import Logger
import collections
import Extractor


def instrument_klee_var_expr(source_path, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\t\tinstrumenting source code")
    orig_variable_list = Extractor.extract_variable_list(source_path, start_line, end_line, only_in_range)
    if not only_in_range:
        syntax_format_command = "clang-tidy " + source_path + " -fix -checks=\"readability-braces-around-statements\""
        ret_code = execute_command(syntax_format_command)
        if int(ret_code) != 0:
            error_exit("SYNTAX FORMAT ERROR IN INSTRUMENTATION")
    formatted_variable_list = Extractor.extract_variable_list(source_path, start_line, end_line, False)
    # print(variable_list)
    insert_code = dict()
    instrument_code = ""
    index = 0
    # TODO: very expensive loop, need to optimize
    for variable, line_number in orig_variable_list:
        insert_line_number = 0
        for formatted_pair in formatted_variable_list:
            form_variable, form_line_number = formatted_pair
            if form_variable == variable:
                insert_line_number = form_line_number
                formatted_variable_list.remove(formatted_pair)
        if insert_line_number in insert_code.keys():
            insert_code[insert_line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
        else:
            insert_code[insert_line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"

    sorted_insert_code = collections.OrderedDict(sorted(insert_code.items(), reverse=True))
    # print(sorted_insert_code)
    #
    # insert_line = 0
    # if Common.Project_B.path in source_path:
    #     insert_line = int(start_line) - 1
    # else:
    #     insert_line = int(end_line) - 1

    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            for insert_line in sorted_insert_code:
                instrument_code = sorted_insert_code[insert_line]
                if insert_line == sorted_insert_code.keys()[0]:
                    instrument_code += "exit(1);\n"
                existing_line = content[insert_line-1]
                content[insert_line-1] = existing_line + instrument_code

    with open(source_path, 'w') as source_file:
        source_file.writelines(content)

    ret_code = 1
    while ret_code != 0:
        syntax_fix_command = "clang-tidy --fix-errors " + source_path
        execute_command(syntax_fix_command)
        syntax_check_command = "clang-tidy " + source_path
        ret_code = int(execute_command(syntax_check_command))
