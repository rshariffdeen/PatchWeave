#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys

sys.path.append('./ast/')
import time
from common.Utilities import error_exit
from common import Definitions
import Generator
from tools import Mapper, Logger, Filter, Emitter, Differ

FILE_EXCLUDED_EXTENSIONS = ""
FILE_EXCLUDED_EXTENSIONS_A = ""
FILE_EXCLUDED_EXTENSIONS_B = ""
FILE_DIFF_C = ""
FILE_DIFF_H = ""
FILE_DIFF_ALL = ""
FILE_AST_SCRIPT = ""
FILE_AST_DIFF_ERROR = ""


diff_info = dict()



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


def get_ast_script(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating AST script")
    Generator.generate_ast_script(source_a, source_b)
    with open(FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        return script_lines


def analyse_source_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    Differ.diff_files()


    extract_h_file_list()
    extract_c_file_list()
    extract_diff_info()


def analyse_ast_diff():
    global diff_info
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    source_path_a = ""
    line_number_a = ""
    source_path_b = ""
    ast_script = ""
    ast_map_a = ""
    ast_map_b = ""
    mapping_ba = ""
    for diff_loc in diff_info.keys():
        source_path, line_number = diff_loc.split(":")
        if source_path != source_path_a:
            Emitter.sub_sub_title(source_path)
            source_path_a = source_path
            line_number_a = line_number
            source_path_b = str(source_path_a).replace(Definitions.VALUE_PATH_A, Definitions.VALUE_PATH_B)
            ast_script = get_ast_script(source_path_a, source_path_b)
            ast_map_a = Generator.get_ast_json(source_path_a)
            ast_map_b = Generator.get_ast_json(source_path_b)
            mapping_ba = Mapper.map_ast_from_source(source_path_a, source_path_b)
        Emitter.normal("\tline number:" + line_number)
        diff_loc_info = diff_info[diff_loc]
        operation = diff_loc_info['operation']
        filtered_ast_script = list()
        if operation == 'insert':
            start_line_b, end_line_b = diff_loc_info['new-lines']
            line_range_b = (start_line_b, end_line_b)
            line_range_a = (-1, -1)
            info_a = (source_path_a, line_range_a, ast_map_a)
            info_b = (source_path_b, line_range_b, ast_map_b)
            filtered_ast_script = Filter.filter_ast_script(ast_script,
                                                           info_a,
                                                           info_b,
                                                           mapping_ba
                                                           )
        elif operation == 'modify':
            line_range_a = diff_loc_info['old-lines']
            line_range_b = diff_loc_info['new-lines']
            info_a = (source_path_a, line_range_a, ast_map_a)
            info_b = (source_path_b, line_range_b, ast_map_b)
            filtered_ast_script = Filter.filter_ast_script(ast_script,
                                                           info_a,
                                                           info_b,
                                                           mapping_ba
                                                           )
        diff_info[diff_loc]['ast-script'] = filtered_ast_script


def set_values():
    global FILE_DIFF_C, FILE_DIFF_H, FILE_DIFF_ALL
    global FILE_AST_SCRIPT, FILE_AST_DIFF_ERROR
    global FILE_EXCLUDED_EXTENSIONS, FILE_EXCLUDED_EXTENSIONS_A, FILE_EXCLUDED_EXTENSIONS_B



def diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Analysing changes")
    set_values()
    safe_exec(analyse_source_diff, "analysing source diff")
    safe_exec(analyse_ast_diff, "analysing ast diff")
