#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import time
from common import Definitions, Values
from tools import Emitter, Builder, Logger, Exploiter
from phases import Trace
from common.Utilities import error_exit


def build_projects():
    if not Values.SKIP_TRACE_GEN:
        if Values.ASAN_FLAG == "":
            Builder.build_llvm()
            Exploiter.test_exploits()
        else:
            Builder.build_asan()
            Exploiter.test_exploits()
            Builder.build_llvm()
    else:
        Builder.soft_restore_all()


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Emitter.sub_title(title)
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


def build():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Building projects")
    safe_exec(build_projects, "building binaries")
