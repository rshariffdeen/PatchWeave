#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
import Output
import Common
import Logger
import Concolic
import Generator
import Tracer
import Mapper

function_list_a = list()
function_list_b = list()
function_list_c = list()
target_candidate_function_list = list()
filtered_trace_list = list()
insertion_point_list = list()

FILE_VAR_EXPR_LOG = Common.DIRECTORY_OUTPUT + "/log-sym-expr"


def extract_source_list(trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting source file list from trace ...")
    source_list = list()
    for trace_line in trace_list:
        source_path, line_number = str(trace_line).split(":")
        source_path = source_path.strip()
        if source_path not in source_list:
            source_list.append(source_path)
    return source_list


def get_function_map(source_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting function list from source files ...")
    source_function_map = dict()
    for source_path in source_list:
        if source_path in source_function_map.keys():
            continue
        try:
            function_list, definition_list = Generator.parse_ast(source_path, False)
            source_function_map[source_path] = function_list
        except Exception as e:
            error_exit(e, "Error in parse_ast.")

    return source_function_map


def extract_trace_function_list(source_list, trace_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting function list from trace ...")
    trace_function_list = list()
    source_function_map = get_function_map(source_list)
    unique_trace_list = list(set(trace_list))
    source_line_map = dict()
    for trace_line in unique_trace_list:
        source_path, line_number = str(trace_line).split(":")
        if source_path not in source_line_map.keys():
            source_line_map[source_path] = list()
        source_line_map[source_path].append(int(line_number))

    for source_path in source_line_map:
        function_list = source_function_map[source_path]
        trace_line_list = source_line_map[source_path]
        for line_number in trace_line_list:
            for function_name, begin_line, finish_line in function_list:
                if line_number in range(begin_line, finish_line):
                    trace_function = source_path + ":" + function_name
                    trace_function += ":" + str(begin_line) + ":" + str(finish_line)
                    if trace_function not in trace_function_list:
                        trace_function_list.append(trace_function)
    return trace_function_list


def generate_candidate_function_list():
    global filtered_trace_list
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating candidate functions")
    trace_list = Concolic.list_trace_c
    div_point = Concolic.divergent_loc
    length = len(trace_list)
    filtered_trace_list = list()
    for n in range (length-1, 0, -1):
        filtered_trace_list.append(trace_list[n])
        if div_point is trace_list[n]:
            break
    filtered_trace_list.reverse()
    source_list_c = extract_source_list(filtered_trace_list)
    candidate_list = extract_trace_function_list(source_list_c, filtered_trace_list)
    return candidate_list


def transplant_code():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for insertion_loc in insertion_point_list:
        source_path, line_number = insertion_loc.split(":")
        Mapper.generate_symbolic_expressions(source_path, line_number)
        sym_expr_map = Mapper.collect_symbolic_expressions(FILE_VAR_EXPR_LOG)
        print(sym_expr_map)


def get_function_range_from_trace(function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    stack_info = Tracer.stack_c
    range_map = dict()

    for func in function_list:
        source_path, function_name, start_line, end_line = func.split(":")
        function_def = source_path + ":" + function_name
        if function_def not in range_map.keys():
            range_map[function_def] = dict()

        start_line = int(start_line)
        end_line = int(end_line)
        trace_start_line = end_line
        trace_end_line = start_line

        for trace_line in filtered_trace_list:
            if source_path in trace_line:
                line_number = int(trace_line.split(":")[1])
                if line_number in range(start_line, end_line+1):
                    if line_number < trace_start_line:
                        trace_start_line = line_number

                    if trace_end_line < line_number:
                        trace_end_line = line_number

        range_map[function_def]['start'] = int(trace_start_line)
        range_map[function_def]['end'] = int(trace_end_line)

        # if source_path in stack_info.keys():
        #     if function_name in stack_info[source_path].keys():
        #         range_map[function_def]['end'] = int(stack_info[source_path][function_name])

    # print(range_map)
    return range_map


def identify_insertion_points():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global insertion_point_list
    function_list = generate_candidate_function_list()
    stack_info = Tracer.stack_c
    range_map = get_function_range_from_trace(function_list)

    for function_def in range_map:
        start_line = int(range_map[function_def]['start'])
        end_line = int(range_map[function_def]['end'])
        for n in range(start_line, end_line + 1):
            source_path = function_def.split(":")[0]
            insertion_point_list.append(source_path + ":" + str(n))


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title( title + "...")
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


def weave():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("transplanting patch")
    safe_exec(identify_insertion_points, "identifying insertion points")
    safe_exec(transplant_code, "transplanting code")
