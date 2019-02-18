#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common import Values
from ast import ASTGenerator
from common.Utilities import backup_file, restore_file, reset_git
from tools import Logger, Emitter, Instrumentor, Builder, \
    Extractor, KleeExecutor, Filter, Mapper, Finder, Collector, Converter


def generate_symbolic_expressions(source_path, start_line, end_line,
                                  output_log, only_in_range=True):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    if Values.PATH_A in source_path:
        binary_path = Values.PATH_A + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
    elif Values.PATH_B in source_path:
        binary_path = Values.PATH_B + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
    elif Values.PATH_C in source_path:
        binary_path = Values.PATH_C + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])
    else:
        binary_path = Values.Project_D.path + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])

    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    backup_file(binary_path, "original-bitcode")
    Instrumentor.instrument_klee_var_expr(source_path, start_line, end_line, only_in_range)
    Builder.build_instrumented_code(source_directory)
    Converter.convert_binary_to_llvm(binary_path)
    KleeExecutor.generate_var_expressions(binary_args, binary_directory, binary_name, output_log)
    restore_file("original-bitcode", binary_path)
    reset_git(source_directory)


def generate_candidate_function_list(estimate_loc, var_expr_map, trace_list, var_expr_log):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating candidate functions")
    filtered_trace_list = Filter.filter_trace_list_by_loc(trace_list, estimate_loc)
    source_list_c = Extractor.extract_source_list(filtered_trace_list)
    source_function_map = Mapper.map_source_function(source_list_c)
    trace_function_list = Extractor.extract_source_lines_from_trace(filtered_trace_list)
    candidate_function_list = dict()
    for function_id in trace_function_list:
        source_path, function_name = str(function_id).split(":")
        function_info = trace_function_list[function_id]
        begin_line = function_info['begin']
        last_line = function_info['last']
        ast_map_c = ASTGenerator.get_ast_json(source_path)
        # print(int(last_line), source_path)
        function_node = Finder.search_function_node_by_loc(ast_map_c,
                                                           int(last_line),
                                                           source_path)
        # print(function_node)
        generate_symbolic_expressions(source_path,
                                      last_line,
                                      last_line,
                                      var_expr_log,
                                      False)

        sym_expr_map = Collector.collect_symbolic_expressions(var_expr_log)
        var_map = Mapper.map_variable(var_expr_map, sym_expr_map)
        function_id = source_path + ":" + function_name
        info = dict()
        info['var-map'] = var_map
        info['begin-line'] = begin_line
        info['last-line'] = last_line
        info['exec-lines'] = function_info['lines']
        info['score'] = len(var_map)
        candidate_function_list[function_id] = info
    return candidate_function_list
