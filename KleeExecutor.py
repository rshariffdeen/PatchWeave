#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger


SYMBOLIC_CONVERTER = "gen-bout"
SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS_FOR_PATH = "-print-path  -write-smt2s  --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
SYMBOLIC_ARGUMENTS_FOR_EXPR = "-no-exit-on-error --resolve-path --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"

VALUE_BIT_SIZE = 0
VALUE_BINARY_PATH_A = ""
VALUE_BINARY_PATH_B = ""
VALUE_BINARY_PATH_C = ""

FILE_KLEE_LOG_A = ""
FILE_KLEE_LOG_B = ""
FILE_KLEE_LOG_C = ""
FILE_SYM_PATH_A = ""
FILE_SYM_PATH_B = ""
FILE_SYM_PATH_C = ""
FILE_SYMBOLIC_POC = ""


def generate_path_condition(binary_arguments, binary_path, binary_name, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic trace for path conditions")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_PATH
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", FILE_SYMBOLIC_POC) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(VALUE_BIT_SIZE) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)
    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


def generate_var_expressions(binary_arguments, binary_path, binary_name, log_path, indent=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if indent:
        Output.normal("\t\tgenerating symbolic expressions")
    else:
        Output.normal("\t\t\tgenerating symbolic expressions")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS_FOR_EXPR
    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", FILE_SYMBOLIC_POC) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(VALUE_BIT_SIZE) + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    ret_code = execute_command(trace_command)
    if int(ret_code) != 0:
        error_exit("CONCOLIC EXECUTION FAILED with code " + ret_code)





def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title("starting " + title + "...")
    description = title[0].lower() + title[1:]
    try:
        Logger.information("running " + str(function_def))
        if not args:
            result = function_def()
        else:
            result = function_def(*args)
        duration = str(time.time() - start_time)
        Output.success("\n\tSuccessful " + description + ", after " + duration + " seconds.")
    except Exception as exception:
        duration = str(time.time() - start_time)
        Output.error("Crash during " + description + ", after " + duration + " seconds.")
        error_exit(exception, "Unexpected error during " + description + ".")
    return result


def set_values():
    global FILE_KLEE_LOG_A, FILE_KLEE_LOG_B, FILE_KLEE_LOG_C
    global FILE_SYM_PATH_A, FILE_SYM_PATH_B, FILE_SYM_PATH_C
    global FILE_SYMBOLIC_POC
    FILE_KLEE_LOG_A = Common.DIRECTORY_OUTPUT + "/log-klee-pa"
    FILE_KLEE_LOG_B = Common.DIRECTORY_OUTPUT + "/log-klee-pb"
    FILE_KLEE_LOG_C = Common.DIRECTORY_OUTPUT + "/log-klee-pc"
    FILE_SYM_PATH_A = Common.DIRECTORY_OUTPUT + "/sym-path-a"
    FILE_SYM_PATH_B = Common.DIRECTORY_OUTPUT + "/sym-path-b"
    FILE_SYM_PATH_C = Common.DIRECTORY_OUTPUT + "/sym-path-c"
    FILE_SYMBOLIC_POC = Common.DIRECTORY_OUTPUT + "/symbolic.ktest"


def execute():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Concolic execution traces")
    set_values()
    convert_poc()
    safe_exec(generate_trace_donor, "generating symbolic trace information from donor program")
    safe_exec(generate_trace_target, "generating symbolic trace information from target program")
