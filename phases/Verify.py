#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
sys.path.append('./ast/')
import time
from common.Utilities import error_exit
from common import Definitions
from tools import Logger, Emitter, Builder
from phases import Trace


def verify_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Builder.build_verify()


def verify_exploit():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal(Definitions.Project_D.path)
    if Trace.crash_location_c == "":
        Builder.build_asan()
        Emitter.sub_title("verifying exploits")
        target_exit_code, target_output = Trace.run_exploit(Definitions.VALUE_EXPLOIT_C,
                                                            Definitions.Project_D.path,
                                                            Definitions.VALUE_PATH_POC,
                                                            Trace.FILE_EXPLOIT_OUTPUT_D)

        if any(crash_word in target_output.lower() for crash_word in Trace.crash_word_list):
            target_crashed = True
            Emitter.normal("\tprogram crashed with exit code " + str(target_exit_code))
        else:
            if target_exit_code != 0:
                Emitter.normal("\tprogram exited with exit code " + str(target_exit_code))
            else:
                error_exit("program did not crash!!")

    else:
        exit_code, output = Trace.run_exploit(Definitions.VALUE_EXPLOIT_C,
                                              Definitions.Project_D.path,
                                              Definitions.VALUE_PATH_POC,
                                              Trace.FILE_EXPLOIT_OUTPUT_D)
        if int(exit_code) == int(Trace.target_exit_code):
            error_exit("\tprogram crashed with exit code " + str(exit_code))
        else:
            Emitter.normal("\tprogram did not crash!!")
            Emitter.normal("\t\tbefore transplantation exit code " + str(Trace.target_exit_code))
            Emitter.normal("\t\tafter transplantation exit code " + str(exit_code))


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
        Emitter.success("\n\tSuccessful " + description + ", after " + duration + " seconds.")
    except Exception as exception:
        duration = str(time.time() - start_time)
        Emitter.error("Crash during " + description + ", after " + duration + " seconds.")
        error_exit(exception, "Unexpected error during " + description + ".")
    return result


def verify():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Patch Verification")
    safe_exec(verify_compilation, "verifying project build")
    safe_exec(verify_exploit, "verifying exploit")
