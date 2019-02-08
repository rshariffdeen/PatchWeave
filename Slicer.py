#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys

sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, find_files, get_file_extension_list
import Output
import Common
import Generator
import Vector
import Logger
import Differ


def slice_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    print(Differ.diff_info)
    exit()


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


def slice():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Slicing unrelated code")
    safe_exec(slice_diff, "removing unwanted code")
