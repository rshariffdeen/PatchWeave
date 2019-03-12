#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import error_exit
from ast import ASTGenerator
import Generator
import Extractor
import Emitter
import Logger
import Oracle
import Solver


def map_variable(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tgenerating variable map")
    var_map = dict()
    for var_a in var_map_a:
        # print(var_a)
        sym_expr_list_a = var_map_a[var_a]
        candidate_list = list()
        # print(sym_expr_list_a)
        for sym_expr_a in sym_expr_list_a:
            sym_expr_code_a = Generator.generate_z3_code_for_var(sym_expr_a, var_a)
            # print(sym_expr_a)
            input_bytes_a = Extractor.extract_input_bytes_used(sym_expr_code_a)
            # print(input_bytes_a)
            for var_b in var_map_b:
                # print(var_b)
                sym_expr_list_b = var_map_b[var_b]
                # print(sym_expr_list_b)
                for sym_expr_b in sym_expr_list_b:
                    sym_expr_code_b = Generator.generate_z3_code_for_var(sym_expr_b, var_b)
                    # print(sym_expr_b)
                    input_bytes_b = Extractor.extract_input_bytes_used(sym_expr_code_b)
                    # print(input_bytes_b)
                    if input_bytes_a and (input_bytes_a == input_bytes_b):
                        z3_eq_code = Generator.generate_z3_code_for_equivalence(sym_expr_code_a, sym_expr_code_b)
                        if Oracle.is_var_expr_equal(z3_eq_code):
                            candidate_list.append(var_b)
        # print(candidate_list)
        if len(candidate_list) == 1:
            var_map[var_a] = candidate_list[0]
        elif len(candidate_list) > 1:
            distance = 100
            best_candidate = ""
            for var_b in candidate_list:
                l_distance = Solver.levenshtein_distance(var_a, var_b)
                if l_distance < distance:
                    distance = l_distance
                    best_candidate = var_b
                elif l_distance == distance:
                    print(best_candidate, distance)
                    print(var_b, l_distance)
                    error_exit("more than one candidate")
            var_map[var_a] = best_candidate
    return var_map


def map_ast_from_source(source_a, source_b, script_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    ASTGenerator.generate_ast_script(source_a, source_b, script_file_path, True)
    mapping = dict()
    with open(script_file_path, "r") as script_file:
        script_lines = script_file.readlines()
        for script_line in script_lines:
            if "Match" in script_line:
                node_id_a = int(((script_line.split(" to ")[0]).split("(")[1]).split(")")[0])
                node_id_b = int(((script_line.split(" to ")[1]).split("(")[1]).split(")")[0])
                mapping[node_id_b] = node_id_a
    return mapping


def map_source_function(source_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\t\tcollecting function list from source files ...")
    source_function_map = dict()
    for source_path in source_list:
        if source_path in source_function_map.keys():
            continue
        try:
            function_list, definition_list = ASTGenerator.parse_ast(source_path, False)
            source_function_map[source_path] = function_list
        except Exception as e:
            error_exit(e, "Error in parse_ast.")
    return source_function_map
