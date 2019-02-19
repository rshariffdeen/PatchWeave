#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from common.Utilities import error_exit
from common import Values, Definitions
from tools import Logger, Emitter, Verifier
from phases import Trace


def verify_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Verifier.run_compilation()


def verify_exploit():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Verifier.run_exploit(Trace.target_exit_code,
                         Values.EXPLOIT_C,
                         Values.Project_D.path,
                         Values.PATH_POC,
                         Trace.FILE_EXPLOIT_OUTPUT_D,
                         Definitions.crash_word_list,
                         Trace.crash_location_c
                         )


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


def verify():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Patch Verification")
    safe_exec(verify_compilation, "verifying compilation")
    safe_exec(verify_exploit, "verifying exploit")
