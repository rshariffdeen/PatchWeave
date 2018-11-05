#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, find_files, clean_files, get_file_extension_list
import Output
import Common
import Generator
import Vector
import Logger

VALGRIND_INSTRUMENTATION = "valgrind --tool=callgrind "
FILE_VALGRIND_OUTPUT = Common.DIRECTORY_OUTPUT + "/output-valgrind"
FILE_VALGRIND_ERROR = Common.DIRECTORY_OUTPUT + "/error-valgrind"

FILE_VALGRIND_LOG_A = Common.DIRECTORY_OUTPUT + "/callgrind-pa"
FILE_VALGRIND_LOG_B = Common.DIRECTORY_OUTPUT + "/callgrind-pb"
FILE_VALGRIND_LOG_C = Common.DIRECTORY_OUTPUT + "/callgrind-pc"


def run_exploit(exploit, project_path, poc_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    exploit = str(exploit).replace('$POC', poc_path)
    exploit_command = project_path + exploit
    execute_command(exploit_command)


def trace_exploit(exploit, project_path, poc_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("generating execution trace for exploit in " + project_path.split("/")[-2])
    exploit = str(exploit).replace('$POC', poc_path)
    trace_command = VALGRIND_INSTRUMENTATION + project_path + exploit + " > " + FILE_VALGRIND_OUTPUT + \
                    " 2>" + FILE_VALGRIND_ERROR
    execute_command(trace_command)


def extract_function_list(trace_file_path, project_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("extracting function list from trace of " + project_path.split("/")[-1])
    function_list = list()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            found_file = False
            file_path = ""
            for read_line in trace_file:
                read_line = read_line.strip()
                if "fl=" in read_line:
                    file_path = str(read_line).split(") ")[-1]
                    if project_path in file_path:
                        found_file = True
                elif found_file:
                    found_file = False
                    if "fn=" in read_line:
                        function_name = read_line.split(") ")[-1]
                        function_list.append(file_path + ":" + function_name)
    else:
        error_exit("trace file doesn't exists")
    return function_list


def generate_trace_donor():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    trace_exploit(Common.VALUE_EXPLOIT_A, Common.Project_A.path, Common.VALUE_PATH_POC)
    move_command = "mv callgrind* " + FILE_VALGRIND_LOG_A
    execute_command(move_command)
    Common.PROJECT_A_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_A, Common.VALUE_PATH_A)
    trace_exploit(Common.VALUE_EXPLOIT_A, Common.Project_B.path, Common.VALUE_PATH_POC)
    move_command = "mv callgrind* " + FILE_VALGRIND_LOG_B
    execute_command(move_command)
    Common.PROJECT_B_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_B, Common.VALUE_PATH_B)


def generate_trace_target():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    trace_exploit(Common.VALUE_EXPLOIT_C, Common.Project_C.path, Common.VALUE_PATH_POC)
    move_command = "mv callgrind* " + FILE_VALGRIND_LOG_C
    execute_command(move_command)
    Common.PROJECT_C_FUNCTION_LIST = extract_function_list(FILE_VALGRIND_LOG_C, Common.VALUE_PATH_C)


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
    safe_exec(generate_trace_donor, "generating trace information from donor program")
    safe_exec(generate_trace_target, "generating trace information from target program")
