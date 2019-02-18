#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common import Values
from ast import ASTGenerator
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from common.Utilities import backup_file, restore_file, reset_git
from pysmt.shortcuts import get_model
import Logger
import Emitter
import Instrumentor
import Builder
import Extractor
import KleeExecutor
import Filter
import Mapper
import Finder
import Collector
import Converter


def generate_symbolic_expressions(source_path, start_line, end_line,
                                  bit_size, sym_poc_path,
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
    Instrumentor.instrument_klee_var_expr(source_path,
                                          start_line,
                                          end_line,
                                          only_in_range)
    Builder.build_instrumented_code(source_directory)
    Converter.convert_binary_to_llvm(binary_path)

    KleeExecutor.generate_var_expressions(binary_args,
                                          binary_directory,
                                          binary_name,
                                          bit_size,
                                          sym_poc_path,
                                          output_log)
    restore_file("original-bitcode", binary_path)
    reset_git(source_directory)


def generate_candidate_function_list(estimate_loc, var_expr_map,
                                     bit_size, sym_poc_path,
                                     trace_list, var_expr_log):
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
                                      bit_size,
                                      sym_poc_path,
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


def generate_z3_code_for_expr(var_expr, var_name, bit_size):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = var_name + "_" + str(bit_size)
    if bit_size == 64:
        zero = "x0000000000000000"
    else:
        zero = "x00000000"
    code = "(set-logic QF_AUFBV )\n"
    code += "(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
    code += "(declare-fun " + var_name + "() (_ BitVec " + str(bit_size) + "))\n"
    # code += "(declare-fun b () (_ BitVec " + str(bit_size) + "))\n"
    code += "(assert (= " + var_name + " " + var_expr + "))\n"
    # code += "(assert (not (= b #" + zero + ")))\n"
    code += "(assert  (not (= " + var_name + " #" + zero + ")))\n"
    code += "(check-sat)"
    return code


def generate_z3_code(var_expr, var_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = str(var_name).replace("->", "")
    var_name = str(var_name).replace("[", "-")
    var_name = str(var_name).replace("]", "-")
    count_64 = int(var_expr.count("64)"))
    count_bracket = int(var_expr.count(")"))

    if count_bracket == 1:
        if count_64 == 1:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)
        else:
            code = generate_z3_code_for_expr(var_expr, var_name, 32)
    else:

        try:
            code = generate_z3_code_for_expr(var_expr, var_name, 32)
            parser = SmtLibParser()
            script = parser.get_script(cStringIO(code))
            formula = script.get_last_formula()
        except Exception as exception:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)
    return code


def generate_model(str_formula):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(str_formula))
    formula = script.get_last_formula()
    model = get_model(formula, solver_name="z3")
    if not hasattr(model, '__dict__'):
        return None
    return model.__dict__['z3_model']
