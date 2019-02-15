#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from Utilities import execute_command, error_exit
import Output
import Logger


SYMBOLIC_CONVERTER = "gen-bout"
SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS_FOR_PATH = "-print-path  -write-smt2s  --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
SYMBOLIC_ARGUMENTS_FOR_EXPR = "-no-exit-on-error --resolve-path --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
SYMBOLIC_ARGUMENTS_FOR_TRACE = "--posix-runtime --libc=uclibc --print-trace --print-stack "


def generate_path_condition(binary_arguments, binary_path, binary_name, bit_size, poc_path, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic trace for path conditions")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_PATH
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", poc_path) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(bit_size) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)
    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


def generate_var_expressions(binary_arguments, binary_path, binary_name, bit_size, poc_path, log_path, indent=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if indent:
        Output.normal("\t\tgenerating symbolic expressions")
    else:
        Output.normal("\t\t\tgenerating symbolic expressions")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_EXPR
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", poc_path) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(bit_size) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    ret_code = execute_command(trace_command)
    if int(ret_code) != 0:
        error_exit("CONCOLIC EXECUTION FAILED with code " + ret_code)


def generate_trace(exploit_command, binary_path, binary_name, poc_path, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating trace for exploit")
    trace_command = "cd " + binary_path + ";"
    trace_command += SYMBOLIC_ENGINE + SYMBOLIC_ARGUMENTS_FOR_TRACE + " " + binary_name + ".bc "\
                     + exploit_command.replace("$POC", poc_path) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)

