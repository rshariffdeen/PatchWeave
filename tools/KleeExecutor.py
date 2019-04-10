#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import execute_command, error_exit
import Emitter
import Logger


SYMBOLIC_CONVERTER = "gen-bout"
SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS_FOR_PATH = "-print-path  -write-smt2s  --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
SYMBOLIC_ARGUMENTS_FOR_EXPR = " --resolve-path --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
SYMBOLIC_ARGUMENTS_FOR_VALUE = " --resolve-path --libc=uclibc --posix-runtime --external-calls=all"
SYMBOLIC_ARGUMENTS_FOR_TRACE = "--posix-runtime --libc=uclibc --print-trace --print-stack "


def generate_path_condition(binary_arguments, binary_path, binary_name, bit_size, poc_path, log_path, klee_flags):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating symbolic trace for path conditions")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_PATH
    if klee_flags:
        sym_args = sym_args + " " + klee_flags
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", poc_path) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(bit_size) + "  > " + log_path + \
                    " 2>&1"
    # print(klee_flags)
    # print(trace_command)
    execute_command(trace_command)
    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


def generate_var_expressions(binary_arguments, binary_dir, binary_name, bit_size, sym_poc_path, log_path, is_error_on_exit, klee_flags):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    sym_args = ""
    if not is_error_on_exit:
        sym_args = "-no-exit-on-error "
    trace_command = "cd " + binary_dir + ";"
    sym_args += SYMBOLIC_ARGUMENTS_FOR_EXPR
    if klee_flags:
        sym_args = sym_args + " " + klee_flags
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", sym_poc_path) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(bit_size) + "  > " + log_path + \
                    " 2>&1"
    # print(klee_flags)
    # print(trace_command)
    ret_code = execute_command(trace_command)
    if int(ret_code) != 0:
        print("Log Path: " + log_path)
        error_exit("CONCOLIC EXECUTION FAILED with code " + ret_code)


def generate_values(binary_arguments, binary_dir, binary_name, bit_size, poc_path, log_path, is_error_on_exit, klee_flags):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    sym_args = ""
    if not is_error_on_exit:
        sym_args = "-no-exit-on-error "
    trace_command = "cd " + binary_dir + ";"
    sym_args += SYMBOLIC_ARGUMENTS_FOR_VALUE
    if klee_flags:
        sym_args = sym_args + " " + klee_flags
    trace_command += SYMBOLIC_ENGINE + sym_args + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", poc_path) + "  > " + log_path + " 2>&1"
    # print(trace_command)
    ret_code = execute_command(trace_command)
    if int(ret_code) != 0:
        Emitter.warning("\t\tWarning: CONCOLIC EXECUTION FAILED with code " + ret_code)
        print("\t\t\tLog Path: " + log_path)


def generate_trace(exploit_command, binary_path, binary_name, poc_path, log_path, klee_flags, no_exit=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating trace for exploit")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_TRACE
    if klee_flags:
        sym_args = sym_args + " " + klee_flags
    if no_exit:
        sym_args = " --no-exit-on-error " + sym_args
    trace_command += SYMBOLIC_ENGINE + sym_args + " " + binary_name + ".bc "\
                     + exploit_command.replace("$POC", poc_path) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)

