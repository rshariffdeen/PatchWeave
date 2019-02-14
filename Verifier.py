#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger
import Differ
import Builder
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Generator
import Tracer
import Mapper


def verify_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Builder.build_verify()


def verify_exploit():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal(Common.Project_D.path)
    if Tracer.crash_location_c == "":
        Builder.build_asan()
        Output.sub_title("verifying exploits")
        target_exit_code, target_output = Tracer.run_exploit(Common.VALUE_EXPLOIT_C,
                                                             Common.Project_D.path,
                                                             Common.VALUE_PATH_POC,
                                                             Tracer.FILE_EXPLOIT_OUTPUT_D)

        if any(crash_word in target_output.lower() for crash_word in Tracer.crash_word_list):
            target_crashed = True
            Output.normal("\tprogram crashed with exit code " + str(target_exit_code))
        else:
            if target_exit_code != 0:
                Output.normal("\tprogram exited with exit code " + str(target_exit_code))
            else:
                error_exit("program did not crash!!")

    else:
        exit_code, output = Tracer.run_exploit(Common.VALUE_EXPLOIT_C,
                                               Common.Project_D.path,
                                               Common.VALUE_PATH_POC,
                                               Tracer.FILE_EXPLOIT_OUTPUT_D)
        if int(exit_code) == int(Tracer.target_exit_code):
            error_exit("\tprogram crashed with exit code " + str(exit_code))
        else:
            Output.normal("\tprogram did not crash!!")
            Output.normal("\t\tbefore transplantation exit code " + str(Tracer.target_exit_code))
            Output.normal("\t\tafter transplantation exit code " + str(exit_code))


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
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


def verify():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Patch Verification")
    safe_exec(verify_compilation, "verifying project build")
    safe_exec(verify_exploit, "verifying exploit")
