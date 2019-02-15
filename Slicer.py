#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from Utilities import error_exit, get_code
import Output
import Common
import Logger
import Differ
import Tracer
import Extractor
import Oracle
import Concolic


def slice_code_from_trace():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("slicing unrelated diff based on trace")
    for diff_loc in Differ.diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
        skip_lines = list()
        diff_info = Differ.diff_info[diff_loc]
        if 'new-lines' in diff_info.keys():
            start_line, end_line = diff_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            for line_number in line_numbers:
                loc_id = source_file + ":" + str(line_number)
                if loc_id not in Tracer.list_trace_b:
                    if Oracle.is_declaration_line(source_file, line_number):
                        continue
                    statement = get_code(source_file, line_number)

                    if "}" not in statement:
                        skip_lines.append(line_number)
        diff_info['skip-lines'] = skip_lines


def slice_skipped_diff_locs():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    filtered_diff_info = dict()
    for diff_loc in Differ.diff_info:
        diff_info = Differ.diff_info[diff_loc]
        if 'new-lines' in diff_info.keys():
            start_line, end_line = diff_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            skip_lines = diff_info['skip-lines']
            if set(line_numbers) == set(skip_lines):
                continue
        filtered_diff_info[diff_loc] = diff_info
    Differ.diff_info = filtered_diff_info


def slice_function_calls():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("slicing unrelated function calls")
    for diff_loc in Differ.diff_info:
        source_file, start_line = diff_loc.split(":")
        source_file = source_file.replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
        diff_info = Differ.diff_info[diff_loc]
        skip_lines = diff_info['skip-lines']
        if 'new-lines' in diff_info.keys():
            function_call_node_list = Extractor.extract_function_call_list(source_file,
                                                                       start_line)
            start_line, end_line = diff_info['new-lines']
            line_numbers = set(range(int(start_line), int(end_line) + 1))
            for line_number in line_numbers:
                loc_id = source_file + ":" + str(line_number)
                if line_number in function_call_node_list.keys():
                    if not Oracle.is_function_important(source_file,
                                                        function_call_node_list[line_number],
                                                        Concolic.sym_path_b.keys()
                                                        ):
                        skip_lines.append(line_number)
        diff_info['skip-lines'] = skip_lines


def slice_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    slice_code_from_trace()
    slice_skipped_diff_locs()
    slice_function_calls()
    slice_skipped_diff_locs()


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
