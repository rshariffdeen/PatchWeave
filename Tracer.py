#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
import subprocess
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger
import Extractor


SYMBOLIC_ENGINE = "klee --posix-runtime --libc=uclibc --print-trace --print-stack "

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

crash_word_list = ["abort", "core dumped", "crashed"]


def test_exploits():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global donor_exit_code, target_exit_code, donor_crashed, target_crashed
    global FILE_EXPLOIT_OUTPUT_A, FILE_EXPLOIT_OUTPUT_C, crash_word_list
    FILE_EXPLOIT_OUTPUT_A = Common.DIRECTORY_OUTPUT + "/exploit-log-a"
    FILE_EXPLOIT_OUTPUT_C = Common.DIRECTORY_OUTPUT + "/exploit-log-c"
    Output.sub_title("executing exploits")
    Output.normal(Common.Project_A.path)
    donor_exit_code, donor_output = run_exploit(Common.VALUE_EXPLOIT_A, Common.Project_A.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_A)
    if any(crash_word in str(donor_output).lower() for crash_word in crash_word_list):
        donor_crashed = True
        Output.normal("\tprogram crashed with exit code " + str(donor_exit_code))
    else:
        if donor_exit_code != 0:
            Output.normal("\tprogram exited with exit code " + str(donor_exit_code))
            Output.program_output(donor_output)
        else:
            error_exit("program did not crash!!")

    Output.normal(Common.Project_C.path)
    target_exit_code, target_output = run_exploit(Common.VALUE_EXPLOIT_C, Common.Project_C.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_C)
    if any(crash_word in str(target_output).lower() for crash_word in crash_word_list):
        target_crashed = True
        Output.normal("\tprogram crashed with exit code " + str(target_exit_code))
    else:
        if donor_exit_code != 0:
            Output.normal("\tprogram exited with exit code " + str(target_exit_code))
            Output.program_output(target_output)
        else:
            error_exit("program did not crash!!")


def run_exploit(exploit, project_path, poc_path, output_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    exploit = str(exploit).replace('$POC', poc_path)
    exploit_command = project_path + exploit + " > " + output_file_path + " 2>&1"
    # print(exploit_command)
    # Print executed command and execute it in console
    Output.command(exploit_command)
    process = subprocess.Popen([exploit_command], shell=True)
    output, error = process.communicate()
    with open(output_file_path, "r") as output_file:
        output = output_file.readlines()
    # output = subprocess.check_output(exploit_command.split(" "))
    return int(process.returncode), output


def trace_exploit(exploit_command, binary_path, binary_name, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating trace for exploit")
    trace_command = "cd " + binary_path + ";"
    trace_command += SYMBOLIC_ENGINE + " " + binary_name + ".bc "\
                     + exploit_command.replace("$POC", Common.VALUE_PATH_POC)  + "  > " + log_path + \
                    " 2>&1"
    # print(trace_command)
    execute_command(trace_command)


def collect_trace(file_path, project_path, suspicious_loc_list):
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
                        if any(loc in line for loc in suspicious_loc_list):
                            break
    return list_trace


def generate_trace_donor():
    global list_trace_a, list_trace_b, stack_a
    global crash_location_a, donor_suspect_line_list

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_A + Common.VALUE_EXPLOIT_A.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_A)
    crash_location_a = Extractor.extract_crash_point(FILE_TRACE_LOG_A)
    stack_a = Extractor.extract_stack_info(FILE_TRACE_LOG_A)
    if crash_location_a == "":
        donor_suspect_line_list = Extractor.extract_suspicious_points(FILE_EXPLOIT_OUTPUT_A)
    list_trace_a = collect_trace(FILE_TRACE_LOG_A, Common.VALUE_PATH_A, donor_suspect_line_list)
    # print(list_trace_a[-1])
    Output.normal(Common.VALUE_PATH_B)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_B + Common.VALUE_EXPLOIT_A.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_B)
    list_trace_b = collect_trace(FILE_TRACE_LOG_B, Common.VALUE_PATH_B, list())
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
    global target_suspect_line_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    if not Common.NO_SYM_TRACE_GEN:
        binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
        trace_exploit(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, FILE_TRACE_LOG_C)
    crash_location_c = Extractor.extract_crash_point(FILE_TRACE_LOG_C)
    stack_c = Extractor.extract_stack_info(FILE_TRACE_LOG_C)
    if crash_location_c == "":
        target_suspect_line_list = Extractor.extract_suspicious_points(FILE_EXPLOIT_OUTPUT_C)
    list_trace_c = collect_trace(FILE_TRACE_LOG_C, Common.VALUE_PATH_C, target_suspect_line_list)
    # print(list_trace_c[-1])


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


def set_values():
    global FILE_TRACE_LOG_A, FILE_TRACE_LOG_B, FILE_TRACE_LOG_C
    global FILE_EXPLOIT_OUTPUT_A, FILE_EXPLOIT_OUTPUT_C, FILE_EXPLOIT_OUTPUT_D
    FILE_EXPLOIT_OUTPUT_A = Common.DIRECTORY_OUTPUT + "/exploit-log-a"
    FILE_EXPLOIT_OUTPUT_C = Common.DIRECTORY_OUTPUT + "/exploit-log-c"
    FILE_EXPLOIT_OUTPUT_D = Common.DIRECTORY_OUTPUT + "/exploit-log-d"
    FILE_TRACE_LOG_A = Common.DIRECTORY_OUTPUT + "/trace-klee-pa"
    FILE_TRACE_LOG_B = Common.DIRECTORY_OUTPUT + "/trace-klee-pb"
    FILE_TRACE_LOG_C = Common.DIRECTORY_OUTPUT + "/trace-klee-pc"


def trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Analysing execution traces")
    set_values()
    safe_exec(generate_trace_donor, "generating trace information from donor program")
    safe_exec(generate_trace_target, "generating trace information from target program")
