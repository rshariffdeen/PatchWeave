#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from common.Utilities import execute_command, error_exit
from common import Definitions, Values
from tools import Collector, Converter, KleeExecutor, Logger, Emitter

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

sym_path_a = dict()
sym_path_b = dict()
sym_path_c = dict()
estimate_loc_map = dict()


def sym_trace_donor():
    global sym_path_a, sym_path_b
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    project_path_a = Values.PATH_A
    project_path_b = Values.PATH_B
    exploit_a = Values.EXPLOIT_A
    poc_path = Values.PATH_POC
    Emitter.normal(project_path_a)
    klee_flags_a = Values.KLEE_FLAG_A

    if not Values.SKIP_SYM_TRACE_GEN:
        binary_path = project_path_a + exploit_a.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        binary_args = " ".join(exploit_a.split(" ")[1:])
        sym_file_path = KleeExecutor.generate_path_condition(binary_args,
                                                             binary_dir,
                                                             binary_name,
                                                             VALUE_BIT_SIZE,
                                                             FILE_SYMBOLIC_POC,
                                                             FILE_KLEE_LOG_A,
                                                             klee_flags_a)
        copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_A
        execute_command(copy_command)
    sym_path_a = Collector.collect_symbolic_path(FILE_KLEE_LOG_A, project_path_a)
    if not sym_path_a:
        error_exit("No symbolic path for Pa")

    Emitter.normal(project_path_b)
    if not Values.SKIP_SYM_TRACE_GEN:
        binary_path = project_path_b + exploit_a.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        binary_args = " ".join(exploit_a.split(" ")[1:])
        sym_file_path = KleeExecutor.generate_path_condition(binary_args,
                                                             binary_dir,
                                                             binary_name,
                                                             VALUE_BIT_SIZE,
                                                             FILE_SYMBOLIC_POC,
                                                             FILE_KLEE_LOG_B,
                                                             klee_flags_a)
        copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_B
        execute_command(copy_command)
    sym_path_b = Collector.collect_symbolic_path(FILE_KLEE_LOG_B, project_path_b)
    if not sym_path_b:
        error_exit("No symbolic path for Pb")


def sym_trace_target():
    global sym_path_c
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    project_path_c = Values.PATH_C
    exploit_c = Values.EXPLOIT_C
    klee_flags_c = Values.KLEE_FLAG_C
    poc_path = Values.PATH_POC
    Emitter.normal(project_path_c)
    if not Values.SKIP_SYM_TRACE_GEN:
        binary_path = project_path_c + exploit_c.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        binary_args = " ".join(exploit_c.split(" ")[1:])
        sym_file_path = KleeExecutor.generate_path_condition(binary_args,
                                                             binary_dir,
                                                             binary_name,
                                                             VALUE_BIT_SIZE,
                                                             FILE_SYMBOLIC_POC,
                                                             FILE_KLEE_LOG_C,
                                                             klee_flags_c)
        copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_C
        execute_command(copy_command)
    sym_path_c = Collector.collect_symbolic_path(FILE_KLEE_LOG_C, project_path_c)
    if not sym_path_c:
        print(sym_path_c)
        print(FILE_KLEE_LOG_C)
        error_exit("No symbolic path for Pc")


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Emitter.sub_title("starting " + title + "...")
    description = title[0].lower() + title[1:]
    try:
        Logger.information("running " + str(function_def))
        if not args:
            result = function_def()
        else:
            result = function_def(*args)
        duration = str(time.time() - start_time)
        Emitter.success("\n\tSuccessful " + description + ", after " + duration + " seconds.")
    except Exception as exception:
        duration = str(time.time() - start_time)
        Emitter.error("Crash during " + description + ", after " + duration + " seconds.")
        error_exit(exception, "Unexpected error during " + description + ".")
    return result


def set_values():
    global FILE_KLEE_LOG_A, FILE_KLEE_LOG_B, FILE_KLEE_LOG_C
    global FILE_SYM_PATH_A, FILE_SYM_PATH_B, FILE_SYM_PATH_C
    global FILE_SYMBOLIC_POC, VALUE_BIT_SIZE
    FILE_KLEE_LOG_A = Definitions.DIRECTORY_OUTPUT + "/log-klee-pa"
    FILE_KLEE_LOG_B = Definitions.DIRECTORY_OUTPUT + "/log-klee-pb"
    FILE_KLEE_LOG_C = Definitions.DIRECTORY_OUTPUT + "/log-klee-pc"
    FILE_SYM_PATH_A = Definitions.DIRECTORY_OUTPUT + "/sym-path-a"
    FILE_SYM_PATH_B = Definitions.DIRECTORY_OUTPUT + "/sym-path-b"
    FILE_SYM_PATH_C = Definitions.DIRECTORY_OUTPUT + "/sym-path-c"
    FILE_SYMBOLIC_POC = Definitions.DIRECTORY_OUTPUT + "/symbolic.ktest"
    VALUE_BIT_SIZE = Converter.convert_poc_to_ktest(Values.PATH_POC, FILE_SYMBOLIC_POC)


def execute():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Concolic execution traces")
    set_values()

    safe_exec(sym_trace_donor, "generating symbolic trace information from donor program")
    safe_exec(sym_trace_target, "generating symbolic trace information from target program")
