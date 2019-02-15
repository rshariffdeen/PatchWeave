#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys

sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, get_file_extension_list
import Output
import Common
import Generator
import Logger
import Mapper
import Filter


FILE_EXCLUDED_EXTENSIONS = ""
FILE_EXCLUDED_EXTENSIONS_A = ""
FILE_EXCLUDED_EXTENSIONS_B = ""
FILE_DIFF_C = ""
FILE_DIFF_H = ""
FILE_DIFF_ALL = ""
FILE_TEMP_DIFF = ""
FILE_AST_SCRIPT = ""
FILE_AST_DIFF_ERROR = ""


diff_info = dict()


def find_diff_files():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("finding changed files...")
    global FILE_DIFF_H
    extensions = get_file_extension_list(Common.Project_A.path, FILE_EXCLUDED_EXTENSIONS_A)
    extensions = extensions.union(get_file_extension_list(Common.Project_B.path, FILE_EXCLUDED_EXTENSIONS_B))
    with open(FILE_EXCLUDED_EXTENSIONS, 'w') as exclusions:
        for pattern in extensions:
            exclusions.write(pattern + "\n")
    # TODO: Include cases where a file is added or removed
    diff_command = "diff -ENZBbwqr " + Common.Project_A.path + " " + Common.Project_B.path + " -X " \
                   + FILE_EXCLUDED_EXTENSIONS + "> " + FILE_DIFF_ALL + ";"
    diff_command += "cat " + FILE_DIFF_ALL + "| grep -P '\.c and ' > " + FILE_DIFF_C + ";"
    diff_command += "cat " + FILE_DIFF_ALL + "| grep -P '\.h and ' > " + FILE_DIFF_H
    execute_command(diff_command)


def extract_h_file_list():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting changed header files...")
    file_list = list()
    with open(FILE_DIFF_H, 'r') as diff_file:
        diff_line = diff_file.readline().strip()
        while diff_line:
            diff_line = diff_line.split(" ")
            file_a = diff_line[1]
            file_b = diff_line[3]
            Generator.parseAST(file_a, Common.Project_A, is_deckard=True, is_header=True)
            file_list.append(file_a.split("/")[-1])
            diff_line = diff_file.readline().strip()
    if len(file_list) > 0:
        Output.normal("\t\theader files:")
        for h_file in file_list:
            Output.normal("\t\t\t" + h_file)


def extract_diff_info():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tcollecting diff info...")
    with open(FILE_DIFF_C, 'r') as diff_file:
        diff_line = diff_file.readline().strip()
        while diff_line:
            diff_line = diff_line.split(" ")
            file_a = diff_line[1]
            file_b = diff_line[3]
            diff_command = "diff -ENBZbwr " + file_a + " " + file_b + " > " + FILE_TEMP_DIFF
            execute_command(diff_command)
            pertinent_lines_a = []
            pertinent_lines_b = []
            with open(FILE_TEMP_DIFF, 'r') as temp_diff_file:
                file_line = temp_diff_file.readline().strip()
                while file_line:
                    operation = ""
                    # We only want lines starting with a line number
                    if 48 <= ord(file_line[0]) <= 57:
                        # add
                        if 'a' in file_line:
                            line_info = file_line.split('a')
                            operation = "insert"
                        # delete
                        elif 'd' in file_line:
                            line_info = file_line.split('d')
                            operation = "delete"
                        # change (delete + add)
                        elif 'c' in file_line:
                            line_info = file_line.split('c')
                            operation = "modify"

                        # range for file_a
                        line_a = line_info[0].split(',')
                        start_a = int(line_a[0])
                        end_a = int(line_a[-1])

                        # range for file_b
                        line_b = line_info[1].split(',')
                        start_b = int(line_b[0])
                        end_b = int(line_b[-1])

                        diff_loc = file_a + ":" + str(start_a)
                        diff_info[diff_loc] = dict()
                        diff_info[diff_loc]['operation'] = operation

                        if operation == 'insert':
                            diff_info[diff_loc]['new-lines'] = (start_b, end_b)
                        elif operation == "delete":
                            diff_info[diff_loc]['remove-lines'] = (start_a, end_a)
                        elif operation == "modify":
                            diff_info[diff_loc]['old-lines'] = (start_a, end_a)
                            diff_info[diff_loc]['new-lines'] = (start_b, end_b)
                    file_line = temp_diff_file.readline().strip()
            diff_line = diff_file.readline().strip()


def extract_c_file_list():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting changed c/cpp files...")
    file_list = list()
    with open(FILE_DIFF_C, 'r') as diff_file:
        diff_line = diff_file.readline().strip()
        while diff_line:
            diff_line = diff_line.split(" ")
            file_a = diff_line[1]
            file_b = diff_line[3]
            file_list.append(file_a.split("/")[-1])
            diff_line = diff_file.readline().strip()
    if len(file_list) > 0:
        Output.normal("\t\tsource files:")
        for source_file in file_list:
            Output.normal("\t\t\t" + source_file)
    return file_list


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Output.sub_title(title)
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


def get_ast_script(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating AST script")
    Generator.generate_ast_script(source_a, source_b)
    with open(FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        return script_lines


def collect_source_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    find_diff_files()
    extract_h_file_list()
    extract_c_file_list()
    extract_diff_info()


def collect_ast_diff():
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
            Output.sub_sub_title(source_path)
            source_path_a = source_path
            line_number_a = line_number
            source_path_b = str(source_path_a).replace(Common.VALUE_PATH_A, Common.VALUE_PATH_B)
            ast_script = get_ast_script(source_path_a, source_path_b)
            ast_map_a = Generator.get_ast_json(source_path_a)
            ast_map_b = Generator.get_ast_json(source_path_b)
            mapping_ba = Mapper.map_ast_from_source(source_path_a, source_path_b)
        Output.normal("\tline number:" + line_number)
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
        print(diff_loc)
        print(filtered_ast_script)
        diff_info[diff_loc]['ast-script'] = filtered_ast_script


def set_values():
    global FILE_DIFF_C, FILE_DIFF_H, FILE_DIFF_ALL
    global FILE_TEMP_DIFF, FILE_AST_SCRIPT, FILE_AST_DIFF_ERROR
    global FILE_EXCLUDED_EXTENSIONS, FILE_EXCLUDED_EXTENSIONS_A, FILE_EXCLUDED_EXTENSIONS_B
    FILE_EXCLUDED_EXTENSIONS = Common.DIRECTORY_OUTPUT + "/excluded-extensions"
    FILE_EXCLUDED_EXTENSIONS_A = Common.DIRECTORY_OUTPUT + "/excluded-extensions-a"
    FILE_EXCLUDED_EXTENSIONS_B = Common.DIRECTORY_OUTPUT + "/excluded-extensions-b"
    FILE_DIFF_C = Common.DIRECTORY_OUTPUT + "/diff_C"
    FILE_DIFF_H = Common.DIRECTORY_OUTPUT + "/diff_H"
    FILE_DIFF_ALL = Common.DIRECTORY_OUTPUT + "/diff_all"
    FILE_TEMP_DIFF = Common.DIRECTORY_OUTPUT + "/temp_diff"
    FILE_AST_SCRIPT = Common.DIRECTORY_OUTPUT + "/ast-script"
    FILE_AST_DIFF_ERROR = Common.DIRECTORY_OUTPUT + "/errors_ast_diff"


def diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Analysing diff")
    set_values()
    safe_exec(collect_source_diff, "collecting source diff")
    safe_exec(collect_ast_diff, "collecting ast diff")
    print(diff_info)
