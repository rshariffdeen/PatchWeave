#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
import Output
import Common
import Logger
import Builder


SYMBOLIC_CONVERTER = "gen-bout"
WLLVM_EXTRACTOR = "extract-bc"
SYMBOLIC_ENGINE = "klee"
SYMBOLIC_ARGUMENTS = " -write-smt2s -print-trace -print-path --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"


VALUE_BIT_SIZE = 0

FILE_KLEE_LOG_A = Common.DIRECTORY_OUTPUT + "/klee-pa"
FILE_KLEE_LOG_B = Common.DIRECTORY_OUTPUT + "/klee-pb"
FILE_KLEE_LOG_C = Common.DIRECTORY_OUTPUT + "/klee-pc"

FILE_SYM_PATH_A = Common.DIRECTORY_OUTPUT + "/sym-path-a"
FILE_SYM_PATH_B = Common.DIRECTORY_OUTPUT + "/sym-path-b"
FILE_SYM_PATH_C = Common.DIRECTORY_OUTPUT + "/sym-path-c"

FILE_SYMBOLIC_POC = Common.DIRECTORY_OUTPUT + "/symbolic.ktest"

sym_path_a = dict()
sym_path_b = dict()
sym_path_c = dict()

list_trace_a = list()
list_trace_b = list()
list_trace_c = list()


def collect_symbolic_path(file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting symbolic path conditions")
    constraints = dict()
    if os.path.exists(file_path):
        source_path = ""
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[path:condition]' in line:
                    if project_path in line:
                        source_path = str(line.replace("[path:condition]", '')).split(" : ")[0]

                if source_path and "(assert" in line:
                    constraints[source_path] = line
                    source_path = ""

    return constraints


def collect_trace(file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting trace")
    list_trace = list()
    if os.path.exists(file_path):
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[trace]' in line:
                    if project_path in line:
                        if not list_trace or list_trace[-1] is not line:
                            list_trace.append(str(line.replace("[trace]", '')).split(" - ")[0])
    return list_trace


def extract_divergent_point():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting divergent point(s)")
    length = len(list_trace_b)
    for i in range(0, length):
        if list_trace_a[i] is not list_trace_b[i]:
            Common.DIVERGENT_POINT_LIST.append(list_trace_b[i-1])
            # print("Divergent Point: " + list_trace_b[i-1])
            break


def trace_exploit(binary_arguments, binary_path, binary_name, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic trace for exploit")
    trace_command = "cd " + binary_path + ";"
    trace_command += SYMBOLIC_ENGINE + SYMBOLIC_ARGUMENTS.replace("$KTEST", FILE_SYMBOLIC_POC) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(VALUE_BIT_SIZE) + "  > " + log_path + \
                    " 2>&1"
    #print(trace_command)
    execute_command(trace_command)

    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


def extract_bitcode(binary_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    extract_command = WLLVM_EXTRACTOR + " " + binary_path
    execute_command(extract_command)
    return binary_directory, binary_name


def generate_trace_donor():
    global list_trace_a, list_trace_b, list_trace_c
    global sym_path_a, sym_path_b, sym_path_c
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_A + Common.VALUE_EXPLOIT_A.split(" ")[0])
    # sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_A)
    # copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_A
    # execute_command(copy_command)
    list_trace_a = collect_trace(FILE_KLEE_LOG_A, Common.VALUE_PATH_A)
    sym_path_a = collect_symbolic_path(FILE_KLEE_LOG_A, Common.VALUE_PATH_A)

    Output.normal(Common.VALUE_PATH_B)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_B + Common.VALUE_EXPLOIT_A.split(" ")[0])
    # sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_B)
    # copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_B
    # execute_command(copy_command)
    list_trace_b = collect_trace(FILE_KLEE_LOG_B, Common.VALUE_PATH_B)
    sym_path_b = collect_symbolic_path(FILE_KLEE_LOG_B, Common.VALUE_PATH_B)

def generate_trace_target():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
    sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_C)
    copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_C
    execute_command(copy_command)
    list_trace_c = collect_trace(FILE_KLEE_LOG_C, Common.VALUE_PATH_C)
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
    #Builder.build_llvm()
    safe_exec(generate_trace_donor, "generating symbolic trace information from donor program")
    safe_exec(generate_trace_target, "generating symbolic trace information from target program")
    safe_exec(extract_divergent_point, "calculating divergent points")
