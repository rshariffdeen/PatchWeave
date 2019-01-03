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


VALGRIND_INSTRUMENTATION = "valgrind --tool=callgrind "
CALLGRIND_ANNOTATE = "callgrind_annotate"
FILE_VALGRIND_OUTPUT = Common.DIRECTORY_OUTPUT + "/output-valgrind"
FILE_VALGRIND_ERROR = Common.DIRECTORY_OUTPUT + "/error-valgrind"
FILE_CALLGRIND_OUTPUT = Common.DIRECTORY_OUTPUT + "/output-callgrind"
FILE_CALLGRIND_ERROR = Common.DIRECTORY_OUTPUT + "/error-callgrind"

FILE_VALGRIND_LOG_A = Common.DIRECTORY_OUTPUT + "/callgrind-pa"
FILE_VALGRIND_LOG_B = Common.DIRECTORY_OUTPUT + "/callgrind-pb"
FILE_VALGRIND_LOG_C = Common.DIRECTORY_OUTPUT + "/callgrind-pc"

FILE_EXPLOIT_OUTPUT_A = Common.DIRECTORY_OUTPUT + "/exploit-a"
FILE_EXPLOIT_OUTPUT_C = Common.DIRECTORY_OUTPUT + "/exploit-c"


def test_exploits():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.sub_title("exploiting crashes")
    Output.normal(Common.Project_A.path)
    exit_code = run_exploit(Common.VALUE_EXPLOIT_A, Common.Project_A.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_A)
    if exit_code != 1:
        Output.normal("\tprogram crashed with exit code " + str(exit_code))
    Output.normal(Common.Project_C.path)
    exit_code = run_exploit(Common.VALUE_EXPLOIT_C, Common.Project_C.path, Common.VALUE_PATH_POC, FILE_EXPLOIT_OUTPUT_C)
    if exit_code != 1:
        Output.normal("\tprogram crashed with exit code " + str(exit_code))


def run_exploit(exploit, project_path, poc_path, output_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    exploit = str(exploit).replace('$POC', poc_path)
    exploit_command = project_path + exploit + " > " + output_file
    return execute_command(exploit_command)


def extract_crash_point(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting crash point")
    source_path = ""
    function_name = ""
    line_number = ""
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            grab = False
            for read_line in trace_file:
                read_line = read_line.strip()
                if 'at address' in read_line:
                    grab = True
                    continue
                if grab:
                    read_line = read_line.split("==")[-1]
                    read_line = read_line.split(":")
                    function_name = (read_line[1].split("(")[0]).strip()
                    source_path = read_line[1].split("(")[1]
                    line_number = read_line[2].strip(")")
                    break
    return source_path, function_name, line_number


def trace_exploit(exploit, project_path, poc_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating execution trace for exploit")
    exploit = str(exploit).replace('$POC', poc_path)
    trace_command = VALGRIND_INSTRUMENTATION + project_path + exploit + " > " + FILE_VALGRIND_OUTPUT + \
                    " 2>" + FILE_VALGRIND_ERROR
    execute_command(trace_command)
    source_path, function_name, line_number = extract_crash_point(FILE_VALGRIND_ERROR)
    annotate_command = CALLGRIND_ANNOTATE + " callgrind.out.* > " + FILE_CALLGRIND_OUTPUT + \
                    " 2>" + FILE_CALLGRIND_ERROR
    execute_command(annotate_command)
    remove_command = "rm callgrind.out.*"
    execute_command(remove_command)
    return source_path, function_name, line_number


def extract_function_list(trace_file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting function list from trace")
    function_list = list()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            is_trace = False
            file_path = ""
            for read_line in trace_file:
                read_line = read_line.strip()
                if is_trace:
                    break
                if "Ir  file:function" in read_line:
                    is_trace = True

            for read_line in trace_file:
                split_tokens = read_line.split(" ")
                for token in split_tokens:
                    if ":" in token:
                        function_f = token
                        break
                file_path, function_name = str(function_f).split(":")
                if project_path in file_path:
                    if function_f not in function_list:
                        function_list.append(function_f)

    else:
        error_exit("trace file doesn't exists")
    return function_list


def generate_trace_donor():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    prepare_exploit_environment(Common.VALUE_PATH_A)
    source_path, function_name, line_number = trace_exploit(Common.VALUE_EXPLOIT_A, Common.Project_A.path, Common.VALUE_PATH_POC)
    Common.TRACE_LIST[Common.Project_A.name] = source_path, function_name, line_number
    move_command = "cp " + FILE_CALLGRIND_OUTPUT + " " + FILE_VALGRIND_LOG_A
    execute_command(move_command)
    Common.PROJECT_A_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_A, Common.VALUE_PATH_A)
    #print(Common.PROJECT_A_FUNCTION_LIST)

    Output.normal(Common.VALUE_PATH_B)
    prepare_exploit_environment(Common.VALUE_PATH_B)
    source_path, function_name, line_number = trace_exploit(Common.VALUE_EXPLOIT_A, Common.Project_B.path, Common.VALUE_PATH_POC)
    move_command = "cp " + FILE_CALLGRIND_OUTPUT + " " + FILE_VALGRIND_LOG_B
    execute_command(move_command)
    Common.PROJECT_B_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_B, Common.VALUE_PATH_B)


def generate_trace_target():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    source_path, function_name, line_number= trace_exploit(Common.VALUE_EXPLOIT_C, Common.Project_C.path, Common.VALUE_PATH_POC)
    Common.TRACE_LIST[Common.Project_C.name] = source_path, function_name, line_number
    move_command = "cp " + FILE_CALLGRIND_OUTPUT + " " + FILE_VALGRIND_LOG_C
    execute_command(move_command)
    Common.PROJECT_C_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_C, Common.VALUE_PATH_C)


def prepare_exploit_environment(project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if Common.VALUE_EXPLOIT_PREPARE is not None:
        prepare_command = str(Common.VALUE_EXPLOIT_PREPARE).replace("$DIR", project_path) + " >output/null 2>output/null "
        #print(prepare_command)
        execute_command(prepare_command)


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


def trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Analysing execution traces")
    # Builder.build_normal()
    test_exploits()
    safe_exec(generate_trace_donor, "generating trace information from donor program")
    safe_exec(generate_trace_target, "generating trace information from target program")
