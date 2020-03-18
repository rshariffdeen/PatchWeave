#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common import Values
from ast import ASTGenerator
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from common.Utilities import backup_file, restore_file, reset_git, error_exit
from pysmt.shortcuts import get_model
from common import Values
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
import Merger


def generate_symbolic_expressions(source_path, start_line, end_line,
                                  bit_size, sym_poc_path, poc_path,
                                  output_log_expr, output_log_value, stack_info, skip_lines,
                                  only_in_range=True):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tgenerating variable information")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])
    klee_flags = ""
    # print(sym_poc_path, poc_path)
    if Values.PATH_A + "/" in source_path:
        binary_path = Values.PATH_A + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
        source_directory = Values.PATH_A
        klee_flags = Values.KLEE_FLAG_A
    elif Values.PATH_B in source_path:
        binary_path = Values.PATH_B + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
        source_directory = Values.PATH_B
        klee_flags = Values.KLEE_FLAG_A
    elif Values.PATH_C in source_path:
        binary_path = Values.PATH_C + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])
        source_directory = Values.PATH_C
        klee_flags = Values.KLEE_FLAG_C
    else:
        binary_path = Values.Project_D.path + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])
        source_directory = Values.Project_D.path
        klee_flags = Values.KLEE_FLAG_C

    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    # backup_file(binary_path, "original-bitcode")
    is_error_on_exit = Instrumentor.instrument_klee_var_expr(source_path,
                                                             start_line,
                                                             end_line,
                                                             stack_info,
                                                             skip_lines,
                                                             only_in_range
                                                             )

    Builder.build_instrumented_code(source_directory)
    # print(binary_path)
    Converter.convert_binary_to_llvm(binary_path)
    Emitter.normal("\t\t\tgenerating symbolic expressions for variables")
    KleeExecutor.generate_var_expressions(binary_args,
                                          binary_directory,
                                          binary_name,
                                          bit_size,
                                          sym_poc_path,
                                          output_log_expr,
                                          is_error_on_exit,
                                          klee_flags)
    Emitter.normal("\t\t\tgenerating concrete values for variables")
    KleeExecutor.generate_values(binary_args,
                                 binary_directory,
                                 binary_name,
                                 bit_size,
                                 poc_path,
                                 output_log_value,
                                 is_error_on_exit,
                                 klee_flags)
    # restore_file("original-bitcode", binary_path)
    reset_git(source_directory)


def generate_candidate_function_list(estimate_loc, var_info_a,
                                     bit_size, sym_poc_path, poc_path,
                                     trace_list, var_expr_log, var_value_log, stack_info):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tgenerating candidate function list")
    filtered_trace_list = Filter.filter_trace_list_by_loc(trace_list, estimate_loc)
    source_list_c = Extractor.extract_source_list(filtered_trace_list)
    source_function_map = Mapper.map_source_function(source_list_c)
    trace_function_list = Filter.filter_function_list_using_trace(source_function_map,
                                                                  filtered_trace_list)

    # print(trace_function_list)
    Values.localized_function_list = trace_function_list
    Values.non_localized_function_list = Filter.filter_function_list_using_trace(source_function_map, trace_list)
    candidate_function_list = dict()
    expected_score = 0
    # print(var_info_a)
    for var_name in var_info_a:
        var_expr_list = var_info_a[var_name]['expr_list']
        for var_expr in var_expr_list:
            if "A-data" in var_expr:
                expected_score += 1
                break

    if expected_score == 0 :
        Emitter.warning("\t\t No variable using input-bytes to map in source code")
        expected_score = len(var_info_a.keys())
    best_score = 0
    best_function_info = ""
    best_function_id = ""
    Emitter.warning("\t\texpected score: " + str(expected_score))
    function_count = 0
    for function_id in trace_function_list:
        Emitter.special("\t\t" + function_id)
        function_count = function_count + 1

        source_path, function_name = str(function_id).split(":")
        function_info = trace_function_list[function_id]
        begin_line = function_info['begin']
        last_line = function_info['last']
        # trace_order = function_info['order']

        ast_map_c = ASTGenerator.get_ast_json(source_path)
        if ast_map_c is None:
            Emitter.warning("\t\t\tcompile command found")
            continue
        # print(int(last_line), source_path)
        function_node = Finder.search_function_node_by_loc(ast_map_c,
                                                           int(last_line),
                                                           source_path)
        start_line = function_node['start line']
        # print(function_node)

        if Values.BACKPORT and expected_score == 0:
            info = dict()
            info['var-map'] = dict()
            info['start-line'] = start_line
            info['begin-line'] = begin_line
            info['last-line'] = last_line
            info['exec-lines'] = function_info['lines']
            info['score'] = 0
            info['attempt'] = function_count
            # info['order'] = trace_order
            candidate_function_list[function_id] = info
            return candidate_function_list

        generate_symbolic_expressions(source_path,
                                      start_line,
                                      last_line,
                                      bit_size,
                                      sym_poc_path,
                                      poc_path,
                                      var_expr_log,
                                      var_value_log,
                                      stack_info,
                                      list()
                                      )

        var_value_map = Collector.collect_values(var_value_log)
        # print(var_value_map)
        var_expr_map = Collector.collect_symbolic_expressions(var_expr_log)
        # print(var_expr_map)
        var_info_b = Merger.merge_var_info(var_expr_map, var_value_map)
        # print(var_info_b)
        # print(sym_expr_map)
        var_map = Mapper.map_variable(var_info_a, var_info_b)
        function_id = source_path + ":" + function_name
        score = len(var_map)
        # print(var_map)
        Emitter.normal("\t\tscore: " + str(score))
        Emitter.emit_var_map(var_map)
        if best_score < score:
            best_score = score
            best_function_id = function_id
            best_function_info = dict()
            best_function_info['var-map'] = var_map
            best_function_info['start-line'] = start_line
            best_function_info['begin-line'] = begin_line
            best_function_info['last-line'] = last_line
            best_function_info['exec-lines'] = function_info['lines']
            best_function_info['score'] = score
            best_function_info['attempt'] = function_count

        if (expected_score == score) and (len(set(var_map.values())) == score):
            if len(var_map.values()) == 1:
                var = var_map.values()[0]
                if ")" in var:
                    if len(var_map.values()[0].split(")")[1]) == 1:
                        continue

            info = dict()
            info['var-map'] = var_map
            info['start-line'] = start_line
            info['begin-line'] = begin_line
            info['last-line'] = last_line
            info['exec-lines'] = function_info['lines']
            info['score'] = score
            info['attempt'] = function_count
            # info['order'] = trace_order
            candidate_function_list[function_id] = info
            return candidate_function_list
    Values.localization_iteration_no = function_count
    if not candidate_function_list:
        Emitter.error("\t\tbest score is " + str(best_score))
        Emitter.warning("\t\tno candidate function, attempting with best score")
        candidate_function_list[best_function_id] = best_function_info
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


def generate_z3_code_for_var(var_expr, var_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = str(var_name).replace("->", "")
    var_name = str(var_name).replace("[", "-")
    var_name = str(var_name).replace("]", "-")
    count_64 = int(var_expr.count("64)"))
    count_bracket = int(var_expr.count(")"))
    extend_32_count = int(var_expr.count("extend 32)"))
    extend_56_count = int(var_expr.count("extend 56)"))

    if count_bracket == 1:
        if count_64 == 1:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)
        else:
            code = generate_z3_code_for_expr(var_expr, var_name, 32)

    elif extend_56_count > 0:
        code = generate_z3_code_for_expr(var_expr, var_name, 64)

    elif extend_32_count > 0:
        if "extend 32" in var_expr.split(") ")[0]:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)
        elif " 64" in var_expr.split(") ")[0]:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)
        else:
            # print(var_expr)
            var_expr = "((_ zero_extend 32) " + var_expr + " )"
            code = generate_z3_code_for_expr(var_expr, var_name, 64)

    else:
        try:
            var_expr_new = "((_ zero_extend 32) " + var_expr + " )"
            code = generate_z3_code_for_expr(var_expr_new, var_name, 64)
            parser = SmtLibParser()
            script = parser.get_script(cStringIO(code))
            formula = script.get_last_formula()
        except Exception as exception:
            code = generate_z3_code_for_expr(var_expr, var_name, 64)



    # else:
    #
    #     try:
    #         code = generate_z3_code_for_expr(var_expr, var_name, 32)
    #         parser = SmtLibParser()
    #         script = parser.get_script(cStringIO(code))
    #         formula = script.get_last_formula()
    #     except Exception as exception:
    #         code = generate_z3_code_for_expr(var_expr, var_name, 64)

    return code


def generate_z3_code_for_equivalence(sym_expr_a, sym_expr_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    lines_a = sym_expr_a.split("\n")
    var_dec_a = lines_a[2]
    sym_expr_a = lines_a[3]
    lines_b = sym_expr_b.split("\n")
    var_dec_b = lines_b[2]
    sym_expr_b = lines_b[3]
    var_name_a = str(var_dec_a.split(" ")[1]).replace("()", "")
    var_name_b = str(var_dec_b.split(" ")[1]).replace("()", "")

    if "_64" in var_name_a:
        if "_32" in var_name_b:
            sym_expr_b = sym_expr_b.replace(var_name_b, var_name_b + "_64_b")
            var_dec_b = var_dec_b.replace(var_name_b, var_name_b + "_64_b")
            var_name_b = var_name_b + "_64_b"
            var_dec_b = var_dec_b.replace("_ BitVec 32", "_ BitVec 64")
            var_expr_b_tokens = sym_expr_b.split(" ")
            var_expr_b_tokens[3] = "((_ zero_extend 32)" + var_expr_b_tokens[3]
            sym_expr_b = " ".join(var_expr_b_tokens)
            sym_expr_b += ")"

    if "_64" in var_name_b:
        if "_32" in var_name_a:
            sym_expr_a = sym_expr_a.replace(var_name_a, var_name_a + "_64_a")
            var_dec_a = var_dec_a.replace(var_name_a, var_name_a + "_64_a")
            var_name_a = var_name_a + "_64_a"
            var_dec_a = var_dec_a.replace("_ BitVec 32", "_ BitVec 64")
            var_expr_a_tokens = sym_expr_a.split(" ")
            var_expr_a_tokens[3] = "((_ zero_extend 32)" + var_expr_a_tokens[3]
            sym_expr_a = " ".join(var_expr_a_tokens)
            sym_expr_a += ")"

    if var_name_a == var_name_b:
        sym_expr_b = sym_expr_b.replace(var_name_b, var_name_b + "_b")
        var_dec_b = var_dec_b.replace(var_name_b, var_name_b + "_b")
        var_name_b = var_name_b + "_b"
        sym_expr_a = sym_expr_a.replace(var_name_a, var_name_a + "_a")
        var_dec_a = var_dec_a.replace(var_name_a, var_name_a + "_a")
        var_name_a = var_name_a + "_a"

    code = "(set-logic QF_AUFBV )\n"
    code += "(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
    code += var_dec_a + "\n"
    code += var_dec_b + "\n"
    code += sym_expr_a + "\n"
    code += sym_expr_b + "\n"
    code += "(assert (= " + var_name_a + " " + var_name_b + "))\n"
    code += "(check-sat)"
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
