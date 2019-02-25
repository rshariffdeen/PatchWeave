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
from ast import ASTGenerator


def instrument_klee_var_expr(source_path, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\t\tinstrumenting source code")
    orig_variable_list = Extractor.extract_variable_list(source_path, start_line, end_line, only_in_range)
    print(orig_variable_list)
    insert_code = dict()
    instrument_code = ""
    # print(source_path, start_line, end_line, only_in_range)
    # if not only_in_range:
    #     ast_map = ASTGenerator.get_ast_json(source_path)
    #     function_node = Finder.search_function_node_by_loc(ast_map, start_line, source_path)
    #     function_name = function_node['identifier']
    #     ast_node = Finder.search_node_by_loc(function_node, start_line)
    #     ast_node_id = ast_node['id']
    #     syntax_format_command = "clang-tidy " + source_path + " -fix -checks=\"readability-braces-around-statements\""
    #     ret_code = execute_command(syntax_format_command)
    #     if int(ret_code) != 0:
    #         error_exit("SYNTAX FORMAT ERROR IN INSTRUMENTATION")
    #
    #     form_ast_map = ASTGenerator.get_ast_json(source_path)
    #     form_function_node = Finder.search_function_node_by_name(form_ast_map, function_name)
    #     form_ast_node = Finder.search_ast_node_by_id(form_function_node, ast_node_id)
    #     format_start_line = form_ast_node['start line']
    #     format_end_line = form_ast_node['end line']
    #     print(source_path, start_line, end_line)
    #     print(source_path, format_start_line, format_end_line)
    #     formatted_variable_list = Extractor.extract_variable_list(source_path, format_start_line, format_end_line, False)
    #
    #     # print(formatted_variable_list)
    #     # print(orig_variable_list)
    #
    #     # TODO: very expensive loop, need to optimize
    #     for variable, line_number in orig_variable_list:
    #         insert_line_number = 0
    #         for formatted_pair in formatted_variable_list:
    #             form_variable, form_line_number = formatted_pair
    #             if form_variable == variable:
    #                 insert_line_number = form_line_number
    #                 formatted_variable_list.remove(formatted_pair)
    #                 break
    #         if insert_line_number in insert_code.keys():
    #             insert_code[
    #                 insert_line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
    #         else:
    #             insert_code[
    #                 insert_line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
    #
    # # print(variable_list)
    # else:
    #     for variable, line_number in orig_variable_list:
    #         if line_number in insert_code.keys():
    #             insert_code[
    #                 line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
    #         else:
    #             insert_code[
    #                 line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"

    for variable, line_number in orig_variable_list:
        if line_number in insert_code.keys():
            insert_code[
                line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
        else:
            insert_code[
                line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"

    sorted_insert_code = collections.OrderedDict(sorted(insert_code.items(), reverse=True))


    #
    # print(sorted_insert_code)
    #
    # insert_line = 0
    # if Common.Project_B.path in source_path:
    #     insert_line = int(start_line) - 1
    # else:
    #     insert_line = int(end_line) - 1

    ast_map = ASTGenerator.get_ast_json(source_path)
    function_node = Finder.search_function_node_by_loc(ast_map, start_line, source_path)
    return_line_list = Extractor.extract_return_line_list(function_node)

    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            for insert_line in sorted_insert_code:
                instrument_code = sorted_insert_code[insert_line]
                if insert_line == sorted_insert_code.keys()[0]:
                    instrument_code += "exit(1);\n"
                existing_line = content[insert_line-1]
                content[insert_line-1] = existing_line + instrument_code
            for return_line in return_line_list:
                instrument_code = "exit(1);\n"
                existing_line = content[return_line - 1]
                content[return_line - 1] = instrument_code + existing_line

    with open(source_path, 'w') as source_file:
        source_file.writelines(content)

    ret_code = 1
    while ret_code != 0:
        syntax_fix_command = "clang-tidy --fix-errors " + source_path
        execute_command(syntax_fix_command)
        syntax_check_command = "clang-tidy " + source_path
        ret_code = int(execute_command(syntax_check_command))
