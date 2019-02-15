#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys

sys.path.append('./ast/')
from common.Utilities import error_exit, backup_file, restore_file, reset_git
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Emitter
from common import Definitions
import Logger
import Generator
from tools import Builder

KLEE_SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS = "--no-exit-on-error --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
TOOL_KLEE_INSTRUMENTATION = "/home/ridwan/workspace/llvm/llvm-7/build/bin/gizmo"

FILE_TEMP_INSTRUMENTED = Definitions.DIRECTORY_TMP + "/temp-instrumented"



def generate_symbolic_expressions(source_path, start_line, end_line, output_log, only_in_range=True):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    if Definitions.Project_A.path in source_path:
        binary_path = Definitions.Project_A.path + Definitions.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Definitions.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Definitions.Project_B.path in source_path:
        binary_path = Definitions.Project_B.path + Definitions.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Definitions.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Definitions.Project_C.path in source_path:
        binary_path = Definitions.Project_C.path + Definitions.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Definitions.VALUE_EXPLOIT_C.split(" ")[1:])
    else:
        binary_path = Definitions.Project_D.path + Definitions.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Definitions.VALUE_EXPLOIT_C.split(" ")[1:])

    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    backup_file(binary_path, "original-bitcode")

    instrument_code_for_klee(source_path, start_line, end_line, only_in_range)
    Builder.build_instrumented_code(source_directory)
    extract_bitcode(binary_path)
    Concolic.generate_var_expressions(binary_args, binary_directory, binary_name, output_log)
    restore_file("original-bitcode", binary_path)
    reset_git(source_directory)


def get_model_from_solver(str_formula):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(str_formula))
    formula = script.get_last_formula()
    model = get_model(formula, solver_name="z3")
    if not hasattr(model, '__dict__'):
        return None
    return model.__dict__['z3_model']


def create_z3_code(var_expr, var_name, bit_size):
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


def generate_z3_code_for_expr(var_expr, var_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = str(var_name).replace("->", "")
    var_name = str(var_name).replace("[", "-")
    var_name = str(var_name).replace("]", "-")
    count_64 = int(var_expr.count("64)"))
    count_bracket = int(var_expr.count(")"))

    if count_bracket == 1:
        if count_64 == 1:
            code = create_z3_code(var_expr, var_name, 64)
        else:
            code = create_z3_code(var_expr, var_name, 32)
    else:

        try:
            code = create_z3_code(var_expr, var_name, 32)
            parser = SmtLibParser()
            script = parser.get_script(cStringIO(code))
            formula = script.get_last_formula()
        except Exception as exception:
            code = create_z3_code(var_expr, var_name, 64)
    return code


def get_input_bytes_used(sym_expr):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    model_a = get_model_from_solver(sym_expr)
    # print(model_a)
    input_byte_list = list()
    if model_a is not None:
        input_byte_list = extract_keys_from_model(model_a)
        if input_byte_list is None:
            script_lines = str(sym_expr).split("\n")
            value_line = script_lines[3]
            tokens = value_line.split("A-data")
            if len(tokens) > 2:
                error_exit("MORE than expected!!")
            else:
                byte_index = ((tokens[1].split(")")[0]).split("bv")[1]).split(" ")[0]
                input_byte_list.append(int(byte_index))
    if input_byte_list:
        input_byte_list.sort()

    return input_byte_list


def map_variable(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tgenerating variable map")
    var_map = dict()
    for var_a in var_map_a:
        # print(var_a)
        sym_expr = generate_z3_code_for_expr(var_map_a[var_a], var_a)
        # print(sym_expr)
        input_bytes_a = get_input_bytes_used(sym_expr)
        # print(input_bytes_a)
        candidate_list = list()
        for var_b in var_map_b:
            # print(var_b)
            sym_expr = generate_z3_code_for_expr(var_map_b[var_b], var_b)
            # print(sym_expr)
            input_bytes_b = get_input_bytes_used(sym_expr)
            # print(input_bytes_b)
            if input_bytes_a and input_bytes_a == input_bytes_b:
                candidate_list.append(var_b)
        if len(candidate_list) == 1:
            var_map[var_a] = candidate_list[0]
        elif len(candidate_list) > 1:
            print(candidate_list)
            error_exit("more than one candidate")
    return var_map


def map_ast_from_source(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Generator.generate_ast_script(source_a, source_b, FILE_AST_SCRIPT, True)
    mapping = dict()
    with open(FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        for script_line in script_lines:
            if "Match" in script_line:
                node_id_a = int(((script_line.split(" to ")[0]).split("(")[1]).split(")")[0])
                node_id_b = int(((script_line.split(" to ")[1]).split("(")[1]).split(")")[0])
                mapping[node_id_b] = node_id_a
    return mapping

