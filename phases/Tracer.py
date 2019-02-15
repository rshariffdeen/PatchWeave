#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import subprocess
sys.path.append('./ast/')
import time
from common.Tools import error_exit
from common import Vault
from utilities import Collector, Converter, KleeExecutor, Logger, Output

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
    FILE_EXPLOIT_OUTPUT_A = Vault.DIRECTORY_OUTPUT + "/exploit-log-a"
    FILE_EXPLOIT_OUTPUT_C = Vault.DIRECTORY_OUTPUT + "/exploit-log-c"
    Output.sub_title("executing exploits")
    Output.normal(Vault.Project_A.path)
    donor_exit_code, donor_output = run_exploit(Vault.VALUE_EXPLOIT_A, Vault.Project_A.path, Vault.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_A)
    if any(crash_word in str(donor_output).lower() for crash_word in crash_word_list):
        donor_crashed = True
        Output.normal("\tprogram crashed with exit code " + str(donor_exit_code))
    else:
        if donor_exit_code != 0:
            Output.normal("\tprogram exited with exit code " + str(donor_exit_code))
            Output.program_output(donor_output)
        else:
            error_exit("program did not crash!!")

    Output.normal(Vault.Project_C.path)
    target_exit_code, target_output = run_exploit(Vault.VALUE_EXPLOIT_C, Vault.Project_C.path, Vault.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_C)
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


def generate_trace_donor():
    global list_trace_a, list_trace_b, stack_a
    global crash_location_a, donor_suspect_line_list

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Vault.VALUE_PATH_A)
    if not Vault.NO_SYM_TRACE_GEN:
        binary_path = Vault.VALUE_PATH_A + Vault.VALUE_EXPLOIT_A.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        exploit_command = " ".join(Vault.VALUE_EXPLOIT_A.split(" ")[1:])
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    Vault.VALUE_PATH_POC,
                                    FILE_TRACE_LOG_A)
    crash_location_a = Collector.collect_crash_point(FILE_TRACE_LOG_A)
    stack_a = Collector.collect_stack_info(FILE_TRACE_LOG_A)
    if crash_location_a == "":
        donor_suspect_line_list = Collector.collect_suspicious_points(FILE_EXPLOIT_OUTPUT_A)
    list_trace_a = Collector.collect_trace(FILE_TRACE_LOG_A,
                                           Vault.VALUE_PATH_A,
                                           donor_suspect_line_list)
    # print(list_trace_a[-1])
    Output.normal(Vault.VALUE_PATH_B)
    if not Vault.NO_SYM_TRACE_GEN:
        binary_path = Vault.VALUE_PATH_B + Vault.VALUE_EXPLOIT_A.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        exploit_command = " ".join(Vault.VALUE_EXPLOIT_A.split(" ")[1:])
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    Vault.VALUE_PATH_POC,
                                    FILE_TRACE_LOG_B)
    list_trace_b = Collector.collect_trace(FILE_TRACE_LOG_B,
                                           Vault.VALUE_PATH_B,
                                           list())


def generate_trace_target():
    global list_trace_c, crash_location_c, stack_c
    global target_suspect_line_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Vault.VALUE_PATH_C)
    if not Vault.NO_SYM_TRACE_GEN:
        binary_path = Vault.VALUE_PATH_C + Vault.VALUE_EXPLOIT_C.split(" ")[0]
        binary_dir, binary_name = Converter.convert_binary_to_llvm(binary_path)
        exploit_command = " ".join(Vault.VALUE_EXPLOIT_C.split(" ")[1:])
        KleeExecutor.generate_trace(exploit_command,
                                    binary_dir,
                                    binary_name,
                                    Vault.VALUE_PATH_POC,
                                    FILE_TRACE_LOG_C)
    crash_location_c = Collector.collect_crash_point(FILE_TRACE_LOG_C)
    stack_c = Collector.collect_stack_info(FILE_TRACE_LOG_C)
    if crash_location_c == "":
        target_suspect_line_list = Collector.collect_suspicious_points(FILE_EXPLOIT_OUTPUT_C)
    list_trace_c = Collector.collect_trace(FILE_TRACE_LOG_C,
                                           Vault.VALUE_PATH_C,
                                           target_suspect_line_list)
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
    FILE_EXPLOIT_OUTPUT_A = Vault.DIRECTORY_OUTPUT + "/exploit-log-a"
    FILE_EXPLOIT_OUTPUT_C = Vault.DIRECTORY_OUTPUT + "/exploit-log-c"
    FILE_EXPLOIT_OUTPUT_D = Vault.DIRECTORY_OUTPUT + "/exploit-log-d"
    FILE_TRACE_LOG_A = Vault.DIRECTORY_OUTPUT + "/trace-klee-pa"
    FILE_TRACE_LOG_B = Vault.DIRECTORY_OUTPUT + "/trace-klee-pb"
    FILE_TRACE_LOG_C = Vault.DIRECTORY_OUTPUT + "/trace-klee-pc"


def trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Analysing execution traces")
    set_values()
    safe_exec(generate_trace_donor, "generating trace information from donor program")
    safe_exec(generate_trace_target, "generating trace information from target program")
