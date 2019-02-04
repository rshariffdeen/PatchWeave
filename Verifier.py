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


def verify():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Patch Verification")
    # safe_exec(generate_trace_donor, "generating symbolic trace information from donor program")
    # safe_exec(generate_trace_target, "generating symbolic trace information from target program")
