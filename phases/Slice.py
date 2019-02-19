#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from common.Utilities import error_exit
from common import Definitions, Values
import Trace
from tools import Logger, Emitter, Slicer
from phases import Analyse
import Concolic


def remove_code():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("slicing unrelated diff based on trace")

    path_a = Values.PATH_A
    path_b = Values.PATH_B
    trace_list = Trace.list_trace_b
    diff_info = Analyse.diff_info
    diff_info = Slicer.slice_code_from_trace(diff_info, trace_list, path_a, path_b)
    Analyse.diff_info = Slicer.slice_skipped_diff_locs(diff_info)


def remove_func_calls():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("slicing unrelated function calls")
    path_a = Values.PATH_A
    path_b = Values.PATH_B
    sym_path_list = Concolic.sym_path_b.keys()
    diff_info = Analyse.diff_info
    diff_info = Slicer.slice_function_calls(diff_info, sym_path_list, path_a, path_b)
    Analyse.diff_info = Slicer.slice_skipped_diff_locs(diff_info)


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Emitter.sub_title("starting " + title + "...")
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


def slice():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Slicing code")
    safe_exec(remove_code, "slicing code not in trace")
    safe_exec(remove_func_calls, "slicing function calls")
