#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger
import Builder

SYMBOLIC_ENGINE = "klee --print-trace --print-stack "



FILE_VALGRIND_OUTPUT = Common.DIRECTORY_OUTPUT + "/output-valgrind"
FILE_VALGRIND_ERROR = Common.DIRECTORY_OUTPUT + "/error-valgrind"
FILE_CALLGRIND_OUTPUT = Common.DIRECTORY_OUTPUT + "/output-callgrind"
FILE_CALLGRIND_ERROR = Common.DIRECTORY_OUTPUT + "/error-callgrind"

FILE_VALGRIND_LOG_A = Common.DIRECTORY_OUTPUT + "/callgrind-pa"
FILE_VALGRIND_LOG_B = Common.DIRECTORY_OUTPUT + "/callgrind-pb"
FILE_VALGRIND_LOG_C = Common.DIRECTORY_OUTPUT + "/callgrind-pc"

FILE_EXPLOIT_OUTPUT_A = Common.DIRECTORY_OUTPUT + "/exploit-a"
FILE_EXPLOIT_OUTPUT_C = Common.DIRECTORY_OUTPUT + "/exploit-c"

FILE_TRACE_LOG_A = Common.DIRECTORY_OUTPUT + "/trace-klee-pa"
FILE_TRACE_LOG_B = Common.DIRECTORY_OUTPUT + "/trace-klee-pb"
FILE_TRACE_LOG_C = Common.DIRECTORY_OUTPUT + "/trace-klee-pc"

list_trace_a = list()
list_trace_b = list()
list_trace_c = list()

stack_a = dict()
stack_c = dict()

crash_location_a = ""
divergent_location_list = list()
crash_location_c = ""


def test_exploits():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.Project_A.path)
    exit_code = run_exploit(Common.VALUE_EXPLOIT_A, Common.Project_A.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_A)
    if exit_code != 1:
        Output.normal("\tprogram crashed with exit code " + str(exit_code))
    else:
        error_exit("program did not crash!!")

    Output.normal(Common.Project_C.path)
    exit_code = run_exploit(Common.VALUE_EXPLOIT_C, Common.Project_C.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_C)
    if exit_code != 0:
        Output.normal("\tprogram crashed with exit code " + str(exit_code))
    else:
        error_exit("program did not crash!!")


def run_exploit(exploit, project_path, poc_path, output_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    exploit = str(exploit).replace('$POC', poc_path)
    exploit_command = project_path + exploit + " > " + output_file
    # print(exploit_command)
    return execute_command(exploit_command)


def extract_stack_info(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting stack information")
    stack_map = dict()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            is_stack = False
            for read_line in trace_file:
                if is_stack and '#' in read_line:
                    read_line, source_path = str(read_line).split(" at ")
                    source_path, line_number = source_path.split(":")
                    function_name = str(read_line.split(" in ")[1]).split(" (")[0]
                    if source_path not in stack_map.keys():
                        stack_map[source_path] = dict()
                    stack_map[source_path][function_name] = line_number
                if "Stack:" in read_line:
                    is_stack = True
                    continue
    return stack_map


def extract_crash_point(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting crash point")
    crash_location = ""
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            for read_line in trace_file:
                if "KLEE: ERROR:" in read_line:
                    read_line = read_line.replace("KLEE: ERROR: ", "")
                    crash_location = read_line.split(": ")[0]
                    break
    return crash_location


def trace_exploit(exploit_command, binary_path, binary_name, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating trace for exploit")
    trace_command = "cd " + binary_path + ";"
    trace_command += SYMBOLIC_ENGINE + " " + binary_name + ".bc "\
                     + exploit_command.replace("$POC", Common.VALUE_PATH_POC)  + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)


def collect_trace(file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting trace")
    list_trace = list()
    if os.path.exists(file_path):
        with open(file_path, 'r') as trace_file:
            for line in trace_file:
                if '[trace]' in line:
                    if project_path in line:
                        trace_line = str(line.replace("[trace]", '')).split(" - ")[0]
                        trace_line = trace_line.strip()
                        if (not list_trace) or (list_trace[-1] != trace_line):
                            list_trace.append(trace_line)
    return list_trace


def generate_trace_donor():
    global list_trace_a, list_trace_b, stack_a
    global crash_location_a, divergent_location

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_A + Common.VALUE_EXPLOIT_A.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_A)
    list_trace_a = collect_trace(FILE_TRACE_LOG_A, Common.VALUE_PATH_A)
    crash_location_a = extract_crash_point(FILE_TRACE_LOG_A)
    stack_a = extract_stack_info(FILE_TRACE_LOG_A)

    Output.normal(Common.VALUE_PATH_B)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_B + Common.VALUE_EXPLOIT_A.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_B)
    list_trace_b = collect_trace(FILE_TRACE_LOG_B, Common.VALUE_PATH_B)
    # extract_divergent_point()


def extract_divergent_point():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting divergent point(s)")
    global divergent_location_list
    length_a = len(list_trace_a)
    length_b = len(list_trace_b)
    print(length_a, length_b)
    source_loc = ""
    gap = 0
    for i in range(0, length_a):
        trace_line_a = str(list_trace_a[i]).replace(Common.VALUE_PATH_A, "")
        found_diff = False
        if gap >= length_b - i:
            gap = 0;
        for j in range(i + gap, length_b):
            trace_line_b = str(list_trace_b[j]).replace(Common.VALUE_PATH_B, "")
            if trace_line_a == trace_line_b:
                break;
            elif found_diff:
                gap += 1;
            else:
                source_loc = list_trace_a[i]
                print("\t\tdivergent Point:\n\t\t " + source_loc)
                print(i, j, gap)
                print(trace_line_a, trace_line_b)
                divergent_location_list.append(source_loc)
                found_diff = True
    print(divergent_location_list)


def generate_trace_target():
    global list_trace_c, crash_location_c, stack_c

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_C)
    list_trace_c = collect_trace(FILE_TRACE_LOG_C, Common.VALUE_PATH_C)
    crash_location_c = extract_crash_point(FILE_TRACE_LOG_C)
    stack_c = extract_stack_info(FILE_TRACE_LOG_C)


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title(title + "...")
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


def trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Analysing execution traces")
    # Builder.build_normal()
    safe_exec(test_exploits, "testing crash case")
    safe_exec(generate_trace_donor, "generating trace information from donor program")
    safe_exec(generate_trace_target, "generating trace information from target program")
