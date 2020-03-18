#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from common.Utilities import error_exit
from common import Values, Definitions
from tools import Logger, Emitter, Verifier, Fuzzer, Writer
from phases import Trace, Exploit

DIR_FUZZ_INPUT = ""
DIR_FUZZ_OUTPUT_LOG = ""
FILE_FUZZ_RESULT = ""
FILE_OUTPUT_DIFF = ""
ITERATION_COUNT = 5


def verify_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Verifier.run_compilation()


def verify_exploit():
    global FILE_OUTPUT_DIFF
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    target_trace_info = Exploit.target_exit_code, Exploit.target_crashed, Exploit.FILE_EXPLOIT_OUTPUT_C
    output_c, output_d = Verifier.run_exploit(target_trace_info,
                                              Values.EXPLOIT_C,
                                              Values.Project_D.path,
                                              Values.PATH_POC,
                                              Exploit.FILE_EXPLOIT_OUTPUT_D,
                                              Definitions.crash_word_list,
                                              Trace.crash_location_c
                                              )
    with open(FILE_OUTPUT_DIFF, 'w') as diff_file:
        diff_file.writelines(output_c)
        diff_file.writelines(["\n-----------------------\n"])
        diff_file.writelines(output_d)


def verify_behavior():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    total_errors = 0
    total_fixes = 0
    for i in range(0, ITERATION_COUNT):
        Emitter.sub_sub_title("Iteration " + str(i+1))
        file_extension = Fuzzer.generate_files(Values.PATH_POC, DIR_FUZZ_INPUT)
        fixes, errors = Verifier.differential_test(file_extension, DIR_FUZZ_INPUT, Values.EXPLOIT_C,
                               Values.PATH_C, Values.Project_D.path, DIR_FUZZ_OUTPUT_LOG)
        total_errors += errors
        total_fixes += fixes
        Values.fuzz_results[i] = dict()
        Values.fuzz_results[i]['pass'] = fixes
        Values.fuzz_results[i]['fail'] = errors

    Values.fuzz_results[ITERATION_COUNT] = dict()
    Values.fuzz_results[ITERATION_COUNT]['pass'] = total_fixes/int(ITERATION_COUNT)
    Values.fuzz_results[ITERATION_COUNT]['fail'] = total_errors/int(ITERATION_COUNT)

    Emitter.sub_sub_title("Summary")
    Emitter.statistics("\t\tTotal test: " + str(100 * int(ITERATION_COUNT)))
    Emitter.statistics("\t\tTotal test that passed only in Pd: " + str(total_fixes))
    Emitter.statistics("\t\tTotal test that failed only in Pd: " + str(total_errors))
    Emitter.statistics("\t\tAverage test that passed only in Pd: " + str(total_fixes/int(ITERATION_COUNT)))
    Emitter.statistics("\t\tAverage test that failed only in Pd: " + str(total_errors/int(ITERATION_COUNT)))


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
    global DIR_FUZZ_INPUT, DIR_FUZZ_OUTPUT_LOG
    global FILE_OUTPUT_DIFF, FILE_FUZZ_RESULT
    DIR_FUZZ_INPUT = Definitions.DIRECTORY_OUTPUT + "/fuzz-input"
    DIR_FUZZ_OUTPUT_LOG = Definitions.DIRECTORY_OUTPUT + "/fuzz-output"
    FILE_FUZZ_RESULT = Definitions.DIRECTORY_OUTPUT + "/fuzz-results"
    FILE_OUTPUT_DIFF = Definitions.DIRECTORY_OUTPUT + "/output-diff"


def save_values():
    global FILE_FUZZ_RESULT
    Writer.write_as_json(Values.fuzz_results, FILE_FUZZ_RESULT)


def verify():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Patch Verification")
    set_values()
    if not Values.ONLY_VERIFY:
        safe_exec(verify_compilation, "verifying compilation")
    safe_exec(verify_exploit, "verifying exploit")
    safe_exec(verify_behavior, "verifying differential behavior")
    save_values()

