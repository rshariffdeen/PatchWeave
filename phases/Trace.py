#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import subprocess
sys.path.append('./ast/')
import time
from common.Utilities import error_exit
from common import Definitions, Values
from tools import Collector, Converter, KleeExecutor, Logger, Emitter

FILE_EXPLOIT_OUTPUT_A = ""
FILE_EXPLOIT_OUTPUT_C = ""
FILE_EXPLOIT_OUTPUT_D = ""
FILE_TRACE_LOG_A = ""
FILE_TRACE_LOG_B = ""
FILE_TRACE_LOG_C = ""


list_trace_a = list()
list_trace_b = list()
list_trace_c = list()
stack_a = dict()
stack_c = dict()

crash_location_a = ""
divergent_location_list = list()
crash_location_c = ""
donor_exit_code = ""
target_exit_code = ""
donor_crashed = False
target_crashed = False
target_suspect_line_list = list()
donor_suspect_line_list = list()


def trace_donor():
    global list_trace_a, list_trace_b, stack_a
    global crash_location_a, donor_suspect_line_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    project_path_a = Values.PATH_A
    project_path_b = Values.PATH_B
    exploit_a = Values.EXPLOIT_A
    exploit_command = " ".join(exploit_a.split(" ")[1:])
    poc_path = Values.PATH_POC
    Emitter.normal(project_path_a)

    if not Values.NO_SYM_TRACE_GEN:
        binary_path = project_path_a + exploit_a.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    poc_path,
                                    FILE_TRACE_LOG_A)

    crash_location_a = Collector.collect_crash_point(FILE_TRACE_LOG_A)
    stack_a = Collector.collect_stack_info(FILE_TRACE_LOG_A)
    if crash_location_a == "":
        donor_suspect_line_list = Collector.collect_suspicious_points(FILE_EXPLOIT_OUTPUT_A)
    list_trace_a = Collector.collect_trace(FILE_TRACE_LOG_A,
                                           project_path_a,
                                           donor_suspect_line_list)

    # print(list_trace_a[-1])
    Emitter.normal(project_path_b)
    if not Values.NO_SYM_TRACE_GEN:
        binary_path = project_path_b + exploit_a.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    poc_path,
                                    FILE_TRACE_LOG_B)

    list_trace_b = Collector.collect_trace(FILE_TRACE_LOG_B,
                                           project_path_b,
                                           list())


def trace_target():
    global list_trace_c, crash_location_c, stack_c
    global target_suspect_line_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    project_path_c = Values.PATH_C
    exploit_c = Values.EXPLOIT_C
    exploit_command = " ".join(exploit_c.split(" ")[1:])
    poc_path = Values.PATH_POC

    Emitter.normal(project_path_c)
    if not Values.NO_SYM_TRACE_GEN:
        binary_path = project_path_c + exploit_c.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    poc_path,
                                    FILE_TRACE_LOG_C)

    crash_location_c = Collector.collect_crash_point(FILE_TRACE_LOG_C)
    stack_c = Collector.collect_stack_info(FILE_TRACE_LOG_C)
    if crash_location_c == "":
        target_suspect_line_list = Collector.collect_suspicious_points(FILE_EXPLOIT_OUTPUT_C)
    list_trace_c = Collector.collect_trace(FILE_TRACE_LOG_C,
                                           project_path_c,
                                           target_suspect_line_list)
    # print(list_trace_c[-1])


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Emitter.sub_title(title + "...")
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
    global FILE_TRACE_LOG_A, FILE_TRACE_LOG_B, FILE_TRACE_LOG_C
    global FILE_EXPLOIT_OUTPUT_A, FILE_EXPLOIT_OUTPUT_C, FILE_EXPLOIT_OUTPUT_D
    FILE_EXPLOIT_OUTPUT_A = Definitions.DIRECTORY_OUTPUT + "/exploit-log-a"
    FILE_EXPLOIT_OUTPUT_C = Definitions.DIRECTORY_OUTPUT + "/exploit-log-c"
    FILE_EXPLOIT_OUTPUT_D = Definitions.DIRECTORY_OUTPUT + "/exploit-log-d"
    FILE_TRACE_LOG_A = Definitions.DIRECTORY_OUTPUT + "/trace-klee-pa"
    FILE_TRACE_LOG_B = Definitions.DIRECTORY_OUTPUT + "/trace-klee-pb"
    FILE_TRACE_LOG_C = Definitions.DIRECTORY_OUTPUT + "/trace-klee-pc"


def trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Analysing execution traces")
    set_values()
    safe_exec(trace_donor, "tracing donor program")
    safe_exec(trace_target, "tracing target program")
