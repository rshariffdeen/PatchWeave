#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, find_files, clean_files, get_file_extension_list
import Output
import Common
import Generator
import Vector
import Logger


FILE_EXCLUDED_EXTENSIONS = Common.DIRECTORY_OUTPUT + "/excluded-extensions"
FILE_EXCLUDED_EXTENSIONS_A = Common.DIRECTORY_OUTPUT + "/excluded-extensions-a"
FILE_EXCLUDED_EXTENSIONS_B = Common.DIRECTORY_OUTPUT + "/excluded-extensions-b"
FILE_DIFF_C = Common.DIRECTORY_OUTPUT + "diff_H"
FILE_DIFF_H = Common.DIRECTORY_OUTPUT + "diff_C"


def get_function_info(function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    source_file_list = list()
    Output.normal("gathering function information for source files")
    for function_f in function_list:
        source_file, function_name = str(function_f).split(":")
        if source_file not in source_file_list:
            source_file_list.append(source_file)

    function_info_map = dict()
    for source_file in source_file_list:
        Output.normal("\t" + source_file)
        function_info_map[source_file] = dict()
        function_info_list, definition_info_list = Generator.parse_ast(source_file, False)
        for function_name, start_line, finish_line in function_info_list:
            function_info = dict()
            function_name = str(function_name).strip("u\'").strip("\'")
            function_info_map[source_file][function_name] = (start_line, finish_line)

    filtered_function_info_map = dict()
    for function_f in function_list:
        source_file, function_name = str(function_f).split(":")
        if source_file not in filtered_function_info_map.keys():
            filtered_function_info_map[source_file] = dict()
        filtered_function_info_map[source_file][function_name] = function_info_map[source_file][function_name]

    return filtered_function_info_map


def generate_vectors(function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    function_info = get_function_info(function_list)
    Output.normal("generating vector files for")
    for source_file in function_info:
        Output.normal("\t" + source_file + ":")
        for function_name in function_info[source_file]:
            Output.normal("\t\t" + function_name )
            function_range = function_info[source_file][function_name]
            output_file_name = str(source_file).split("/")[-1].strip(".c").strip(".cpp") + "-" + function_name + ".vec"
            output_directory = source_file.strip(str(source_file).split("/")[-1])
            vector_command = Common.TOOL_VECGEN + " --start-line-number " + \
                       str(function_range[0]) + " --end-line-number " + str(function_range[1]) + \
                       " " + source_file + " -o " + output_directory + "/" + output_file_name + \
                       " 2> " + Common.FILE_ERROR_LOG
            execute_command(vector_command)


def normalize_vector(vector):
    total = sum(vector[i] ** 2 for i in range(len(vector))) ** (1 / 2)
    return [i / total for i in vector]


def calculate_vector_distance(vector_a, vector_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    assert (len(vector_a) == len(vector_b))
    return sum(((vector_a[i] - vector_b[i]) ** 2) for i in range(len(vector_a)))


def generate_similarity_matrix(vector, target_vector_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    similarity_matrix = dict()
    for function_f in target_vector_list:
        target_vector = target_vector_list[function_f]
        distance = calculate_vector_distance(vector, target_vector)
        similarity_matrix[function_f] = distance
    return similarity_matrix


def get_vector_list(function_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    vector_file_list = dict()
    for function_f in function_list:
        source_file, function_name = str(function_f).split(":")
        vector_file_name = str(source_file).split("/")[-1].strip(".c").strip(".cpp") + "-" + function_name + ".vec"
        vector_file_path = source_file.strip(str(source_file).split("/")[-1]) + vector_file_name
        with open(vector_file_path, 'r') as vector_file:
            line = vector_file.readline()
            if line:
                vector = [int(s) for s in vector_file.readline().strip().split(" ")]
                vector = normalize_vector(vector)
                vector_file_list[function_f] = vector
    return vector_file_list


def generate_function_map():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    vector_list_a = get_vector_list(Common.PROJECT_A_FUNCTION_LIST)
    vector_list_c = get_vector_list(Common.PROJECT_C_FUNCTION_LIST)
    function_map = dict()
    for vector_name in vector_list_a:
        print(vector_name)
        vector = vector_list_a[vector_name]
        similarity_matrix = generate_similarity_matrix(vector, vector_list_c)
        print(similarity_matrix)
        best_match_function = ""
        minimum_distance = 100000000000000000
        for vector_c_name in similarity_matrix:
            vector_distance = similarity_matrix[vector_c_name]
            if vector_distance < minimum_distance:
                minimum_distance = vector_distance
                best_match_function = vector_c_name
        function_map[vector_name] = best_match_function
    print(function_map)







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


def match():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Finding target function to patch")
    safe_exec(generate_vectors, "vector generation for traced functions in Pa", Common.PROJECT_A_FUNCTION_LIST)
    safe_exec(generate_vectors, "vector generation for traced functions in Pb", Common.PROJECT_B_FUNCTION_LIST)
    safe_exec(generate_vectors, "vector generation for traced functions in Pc", Common.PROJECT_C_FUNCTION_LIST)

    safe_exec(generate_function_map, "finding matching functions from Pa to Pc")

    # safe_exec(generate_diff, "search for affected functions")
    # # Generates vectors for all functions in Pc

    # # Pairwise vector comparison for matching
    # Common.header_file_list_to_patch = safe_exec(clone_detection_header_files, "clone detection for header files")
    # Common.c_file_list_to_patch = safe_exec(clone_detection_for_c_files, "clone detection for C files")

