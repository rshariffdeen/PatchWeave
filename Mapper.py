#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Output
import Common
import Logger
import Concolic
import Generator
import Tracer

KLEE_SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS = "--no-exit-on-error --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
TOOL_KLEE_INSTRUMENTATION = Common.DIRECTORY_TOOLS + "/gizmo/gizmo"
FILE_TEMP_INSTRUMENTED = Common.DIRECTORY_OUTPUT + "/temp-instrumented"

var_expr_map_a = dict()
var_expr_map_b = dict()
var_expr_map_c = dict()


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
                    var_expr_map[var_name] = var_expr
    return var_expr_map


def generate_symbolic_expressions(source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])
    instrument_command = "cd " + source_directory + ";"
    instrument_command += TOOL_KLEE_INSTRUMENTATION + " --line-number=" + str(line_number) + \
                        " -transformation=var -source=" + source_file_name + " > " + FILE_TEMP_INSTRUMENTED
    execute_command(instrument_command)
    exit()
    #
    # generate_command = "cd " + binary_path + ";"
    # generate_command += SYMBOLIC_ENGINE + SYMBOLIC_ARGUMENTS.replace("$KTEST",
    #                                                               FILE_SYMBOLIC_POC) + " " + binary_name + ".bc " \
    #                  + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(
    #     VALUE_BIT_SIZE) + "  > " + log_path + \
    #                  " 2>&1"
    # # print(trace_command)
    # execute_command(trace_command)

def get_model_from_solver(str_formula):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(str_formula))
    formula = script.get_last_formula()
    model = get_model(formula, solver_name="z3")
    if not hasattr(model, '__dict__'):
        return None
    return model.__dict__['z3_model']


def extract_values_from_model(model):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    byte_array = dict()
    for dec in model.decls():
        if dec.name() == "A-data":
            var_list = model[dec].as_list()
            for pair in var_list:
                if type(pair) == list:
                    byte_array[pair[0]] = pair[1]
    return byte_array


def generate_z3_code_for_expr(var_expr):
    code = "(set-logic QF_AUFBV )\n"
    code += "(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
    code += "(declare-fun a () (_ BitVec 32))\n"
    code += "(declare-fun b () (_ BitVec 32))\n"
    code += "(assert (= a " + var_expr + "))\n"
    code += "(assert (not (= b #x00000000)))\n"
    code += "(assert  (= a b) )\n"
    code += "(check-sat)"
    return code


def get_input_bytes_used(sym_expr):
    model_a = get_model_from_solver(sym_expr)
    input_byte_list = list()
    if model_a is not None:
        input_bytes_map = extract_values_from_model(model_a)
        input_byte_list = list(set(input_bytes_map.keys()))
    return input_byte_list


def generate_mapping(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating variable map")
    for var_a in var_map_a:
        sym_expr = generate_z3_code_for_expr(var_map_a[var_a])
        input_bytes_a = get_input_bytes_used(sym_expr)
        candidate_list = list()
        for var_b in var_map_b:
            sym_expr = generate_z3_code_for_expr(var_map_b[var_b])
            input_bytes_b = get_input_bytes_used(sym_expr)
            if input_bytes_a == input_bytes_b:
                candidate_list.append(var_b)

