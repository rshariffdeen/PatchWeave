#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger
import Differ
import Builder
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Generator
import Tracer
import Mapper


SYMBOLIC_CONVERTER = "gen-bout"
SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS = " -write-smt2s  --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"


VALUE_BIT_SIZE = 0
VALUE_BINARY_PATH_A = ""
VALUE_BINARY_PATH_B = ""
VALUE_BINARY_PATH_C = ""

FILE_KLEE_LOG_A = Common.DIRECTORY_OUTPUT + "/log-klee-pa"
FILE_KLEE_LOG_B = Common.DIRECTORY_OUTPUT + "/log-klee-pb"
FILE_KLEE_LOG_C = Common.DIRECTORY_OUTPUT + "/log-klee-pc"


FILE_SYM_PATH_A = Common.DIRECTORY_OUTPUT + "/sym-path-a"
FILE_SYM_PATH_B = Common.DIRECTORY_OUTPUT + "/sym-path-b"
FILE_SYM_PATH_C = Common.DIRECTORY_OUTPUT + "/sym-path-c"

FILE_SYMBOLIC_POC = Common.DIRECTORY_OUTPUT + "/symbolic.ktest"

sym_path_a = dict()
sym_path_b = dict()
sym_path_c = dict()


estimate_loc_map = dict()


def collect_symbolic_path(file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting symbolic path conditions")
    constraints = dict()
    if os.path.exists(file_path):
        source_path = ""
        path_condition = ""
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:condition]' in line:
                    if project_path in line:
                        source_path = str(line.replace("[path:condition]", '')).split(" : ")[0]
                        source_path = source_path.strip()
                        path_condition = str(line.replace("[path:condition]", '')).split(" : ")[1]
                        continue
                if source_path:
                    if "(exit)" not in line:
                        path_condition = path_condition + line
                    else:
                        constraints[source_path] = path_condition
                        source_path = ""
                        path_condition = ""

    return constraints


def concolic_execution(binary_arguments, binary_path, binary_name, log_path, print_path=False, no_error_exit=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global SYMBOLIC_ARGUMENTS
    Output.normal("\tgenerating symbolic trace for exploit")
    trace_command = "cd " + binary_path + ";"
    sym_args = SYMBOLIC_ARGUMENTS
    if print_path:
        sym_args = " -print-path " + sym_args

    if no_error_exit:
        sym_args = " -no-exit-on-error " + sym_args

    trace_command += SYMBOLIC_ENGINE + sym_args.replace("$KTEST", FILE_SYMBOLIC_POC) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(VALUE_BIT_SIZE) + "  > " + log_path + \
                    " 2>&1"
    print(trace_command)
    execute_command(trace_command)
    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


def generate_trace_donor():
    global list_trace_a, list_trace_b, list_trace_c
    global sym_path_a, sym_path_b, sym_path_c
    global function_list_a, function_list_b
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    # binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_A + Common.VALUE_EXPLOIT_A.split(" ")[0])
    # sym_file_path = concolic_execution(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_A, True)
    # copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_A
    # execute_command(copy_command)
    list_trace_a = Tracer.list_trace_a
    sym_path_a = collect_symbolic_path(FILE_KLEE_LOG_A, Common.VALUE_PATH_A)
    # Mapper.var_expr_map_a = Mapper.collect_symbolic_expressions(FILE_KLEE_LOG_A)

    Output.normal(Common.VALUE_PATH_B)
    # binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_B + Common.VALUE_EXPLOIT_A.split(" ")[0])
    # sym_file_path = concolic_execution(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_B, True)
    # copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_B
    # execute_command(copy_command)
    list_trace_b = Tracer.list_trace_b
    sym_path_b = collect_symbolic_path(FILE_KLEE_LOG_B, Common.VALUE_PATH_B)
    # Mapper.var_expr_map_b = Mapper.collect_symbolic_expressions(FILE_KLEE_LOG_B)


def generate_trace_target():
    global sym_path_c, list_trace_c, function_list_c
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    # binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
    # sym_file_path = concolic_execution(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_C, True)
    # copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_C
    # execute_command(copy_command)
    list_trace_c = Tracer.list_trace_c
    sym_path_c = collect_symbolic_path(FILE_KLEE_LOG_C, Common.VALUE_PATH_C)


def convert_poc():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global VALUE_BIT_SIZE
    Output.normal("converting concrete poc to symbolic file")
    concrete_file = open(Common.VALUE_PATH_POC,'rb')
    VALUE_BIT_SIZE = os.fstat(concrete_file.fileno()).st_size
    convert_command = SYMBOLIC_CONVERTER + " --sym-file " + Common.VALUE_PATH_POC
    execute_command(convert_command)
    move_command = "mv file.bout " + FILE_SYMBOLIC_POC
    execute_command(move_command)


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


def execute():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Concolic execution traces")
    convert_poc()
    safe_exec(generate_trace_donor, "generating symbolic trace information from donor program")
    safe_exec(generate_trace_target, "generating symbolic trace information from target program")
