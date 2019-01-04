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
SYMBOLIC_ARGUMENTS = " -write-smt2s --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"


VALUE_BIT_SIZE = 0

FILE_KLEE_LOG_A = Common.DIRECTORY_OUTPUT + "/klee-pa"
FILE_KLEE_LOG_B = Common.DIRECTORY_OUTPUT + "/klee-pb"
FILE_KLEE_LOG_C = Common.DIRECTORY_OUTPUT + "/klee-pc"

FILE_SYM_PATH_A = Common.DIRECTORY_OUTPUT + "/sym-path-a"
FILE_SYM_PATH_B = Common.DIRECTORY_OUTPUT + "/sym-path-b"
FILE_SYM_PATH_C = Common.DIRECTORY_OUTPUT + "/sym-path-c"

FILE_SYMBOLIC_POC = Common.DIRECTORY_OUTPUT + "/symbolic.ktest"


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


def trace_exploit(binary_arguments, binary_path, binary_name, log_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic trace for exploit")
    trace_command = "cd " + binary_path + ";"
    trace_command += SYMBOLIC_ENGINE + SYMBOLIC_ARGUMENTS.replace("$KTEST", FILE_SYMBOLIC_POC) + " " + binary_name + ".bc "\
                     + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(VALUE_BIT_SIZE) + "  > " + log_path + \
                    " 2>&1"
    print(trace_command)
    execute_command(trace_command)
    sym_file_path = binary_path + "/klee-last/test000001.smt2 "
    return sym_file_path


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


def extract_bitcode(binary_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    extract_command = WLLVM_EXTRACTOR + " " + binary_path
    execute_command(extract_command)
    return binary_directory, binary_name


def generate_trace_donor():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_A)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_A + Common.VALUE_EXPLOIT_A.split(" ")[0])
    sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_A)
    copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_A
    execute_command(copy_command)

    Output.normal(Common.VALUE_PATH_B)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_B + Common.VALUE_EXPLOIT_A.split(" ")[0])
    sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_B)
    copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_B
    execute_command(copy_command)


def generate_trace_target():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.VALUE_PATH_C)
    binary_path, binary_name = extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
    sym_file_path = trace_exploit(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, FILE_KLEE_LOG_C)
    copy_command = "cp " + sym_file_path + " " + FILE_SYM_PATH_C
    execute_command(copy_command)


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
