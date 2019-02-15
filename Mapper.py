#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, backup_file, restore_file, extract_bitcode, reset_git, is_intersect
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Output
import Common
import Logger
import Concolic
import Generator
import Builder
import Weaver
import collections
import Differ
import Collector
import z3


KLEE_SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS = "--no-exit-on-error --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
TOOL_KLEE_INSTRUMENTATION = "/home/ridwan/workspace/llvm/llvm-7/build/bin/gizmo"
FILE_TEMP_INSTRUMENTED = Common.DIRECTORY_OUTPUT + "/temp-instrumented"


def instrument_code_for_klee(source_path, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tinstrumenting source code")
    if not only_in_range:
        syntax_format_command = "clang-tidy " + source_path + " -fix -checks=\"readability-braces-around-statements\""
        ret_code = execute_command(syntax_format_command)
        if int(ret_code) != 0:
            error_exit("SYNTAX FORMAT ERROR IN INSTRUMENTATION")
    variable_list = generate_available_variable_list(source_path, start_line, end_line, only_in_range)
    insert_code = dict()
    instrument_code = ""
    for variable, line_number in variable_list:
        if line_number in insert_code.keys():
            insert_code[line_number] += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
        else:
            insert_code[line_number] = "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"

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




def generate_symbolic_expressions(source_path, start_line, end_line, output_log, only_in_range=True):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    if Common.Project_A.path in source_path:
        binary_path = Common.Project_A.path + Common.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Common.Project_B.path in source_path:
        binary_path = Common.Project_B.path + Common.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Common.Project_C.path in source_path:
        binary_path = Common.Project_C.path + Common.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:])
    else:
        binary_path = Common.Project_D.path + Common.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:])

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


def extract_keys_from_model(model):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    byte_list = list()
    k_list = ""
    for dec in model:
        if hasattr(model[dec], "num_entries"):
            k_list = model[dec].as_list()
    for pair in k_list:
        if type(pair) == list:
            byte_list.append(int(str(pair[0])))
    return byte_list


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


def generate_mapping(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating variable map")
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


def get_ast_mapping(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Generator.generate_ast_script(source_a, source_b, True)
    mapping = dict()
    with open(Differ.FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        for script_line in script_lines:
            if "Match" in script_line:
                node_id_a = int(((script_line.split(" to ")[0]).split("(")[1]).split(")")[0])
                node_id_b = int(((script_line.split(" to ")[1]).split("(")[1]).split(")")[0])
                mapping[node_id_b] = node_id_a
    return mapping

