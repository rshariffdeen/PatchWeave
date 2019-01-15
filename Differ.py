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


FILE_EXCLUDED_EXTENSIONS = Common.DIRECTORY_OUTPUT + "/excluded-extensions"
FILE_EXCLUDED_EXTENSIONS_A = Common.DIRECTORY_OUTPUT + "/excluded-extensions-a"
FILE_EXCLUDED_EXTENSIONS_B = Common.DIRECTORY_OUTPUT + "/excluded-extensions-b"
FILE_DIFF_C = Common.DIRECTORY_OUTPUT + "/diff_C"
FILE_DIFF_H = Common.DIRECTORY_OUTPUT + "/diff_H"
FILE_DIFF_ALL = Common.DIRECTORY_OUTPUT + "/diff_all"
FILE_TEMP_DIFF = Common.DIRECTORY_OUTPUT + "/temp_diff"
FILE_AST_SCRIPT = Common.DIRECTORY_OUTPUT + "/ast-script"
FILE_AST_DIFF_ERROR = Common.DIRECTORY_OUTPUT + "/errors_ast_diff"

APP_AST_DIFF = "crochet-diff"
AST_DIFF_SIZE = "1000"


diff_info = dict()


def find_diff_files():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("finding changed files...")
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
            # Generator.convert_to_llvm(file_a)
            # Generator.convert_to_llvm(file_b)
            Generator.parseAST(file_a, Common.Project_A, is_deckard=True, is_header=True)
            file_list.append(file_a.split("/")[-1])
            diff_line = diff_file.readline().strip()
    if len(file_list) > 0:
        Output.normal("\t\theader files:")
        for h_file in file_list:
            Output.normal("\t\t\t" + h_file)


def extract_function_name_list():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\textracting changed function names...")
    function_list = list()
    with open(FILE_DIFF_C, 'r') as diff_file:
        diff_line = diff_file.readline().strip()
        while diff_line:
            diff_line = diff_line.split(" ")
            file_a = diff_line[1]
            file_b = diff_line[3]
            # Generator.convert_to_llvm(file_a)
            # Generator.convert_to_llvm(file_b)
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
                        # Pertinent lines in file_a
                        pertinent_lines_a.append((start_a, end_a))

                        pertinent_lines_b.append((start_b, end_b))
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
            try:
                Generator.get_function_name_list(Common.Project_A, file_a, pertinent_lines_a)
                Generator.get_function_name_list(Common.Project_B, file_b, pertinent_lines_b)

            except Exception as exception:
                error_exit(exception, "failed at finding affected functions.")
            diff_line = diff_file.readline().strip()
    return function_list


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
            # Generator.convert_to_llvm(file_a)
            # Generator.convert_to_llvm(file_b)
            file_list.append(file_a.split("/")[-1])
            diff_line = diff_file.readline().strip()
    if len(file_list) > 0:
        Output.normal("\t\tsource files:")
        for source_file in file_list:
            Output.normal("\t\t" + source_file)
    return file_list


def generate_diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    find_diff_files()
    extract_h_file_list()
    extract_c_file_list()
    extract_function_name_list()


def generate_vector_for_extension(file_extension, output, is_header=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("Generate vectors for " + file_extension + " files in " + Common.Project_C.name + "...")
    # Generates an AST file for each file of extension ext
    find_files(Common.Project_C.path, file_extension, output)
    with open(output, 'r') as file_list:
        file_name = file_list.readline().strip()
        while file_name:
            # Parses it to get useful information and generate vectors
            try:
                Generator.parseAST(file_name, Common.Project_C, use_deckard=True, is_header=is_header)
            except Exception as e:
                error_exit(e, "Unexpected error in parseAST with file:", file_name)
            file_name = file_list.readline().strip()


def generate_vectors():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    # Generates an vector file for each .h file
    generate_vector_for_extension("*\.h", "output/Hfiles", is_header=True)
    Output("\n")
    # Generates an vector file for each .c file
    generate_vector_for_extension("*\.c", "output/Cfiles", is_header=False)


def get_vector_list(project, extension):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if "c" in extension:
        rxt = "C"
    else:
        rxt = "h"

    Output.normal("Getting vectors for " + rxt + " files in " + project.name + "...")
    filepath = "output/vectors_" + rxt + "_" + project.name
    find_files(project.path, extension, filepath)
    with open(filepath, "r", errors='replace') as file:
        files = [vec.strip() for vec in file.readlines()]
    vecs = []
    for i in range(len(files)):
        with open(files[i], 'r', errors='replace') as vec:
            fl = vec.readline()
            if fl:
                v = [int(s) for s in vec.readline().strip().split(" ")]
                v = Vector.Vector.normed(v)
                vecs.append((files[i], v))
    return vecs


def generate_ast_map(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    command = Common.DIFF_COMMAND + "-dump-matches " + source_a + " " + source_b
    if source_a[-1] == "h":
        command += " --"
    command += " 2>> output/errors_clang_diff"
    command += "| grep -P '^Match ' | grep -P '^Match ' > output/ast-map"
    try:
        execute_command(command, False)
    except Exception as exception:
        error_exit(exception, "Unexpected error in generate_ast_map.")


def generate_ast_script(source_a, source_b, dump_matches=False):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    extra_args = " "
    if dump_matches:
        extra_args = " -dump-matches "

    generate_command = APP_AST_DIFF + " -s=" + AST_DIFF_SIZE  + extra_args + \
                       source_a + " " + source_b  + " 2> " + FILE_AST_DIFF_ERROR + \
                       " > " + FILE_AST_SCRIPT
    execute_command(generate_command)


def get_ast_mapping(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    generate_ast_script(source_a, source_b, True)
    mapping = dict()
    with open(FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        for script_line in script_lines:
            if "Match" in script_line:
                node_id_a = int(((script_line.split(" to ")[0]).split("(")[1]).split(")")[0])
                node_id_b = int(((script_line.split(" to ")[1]).split("(")[1]).split(")")[0])
                mapping[node_id_b] = node_id_a
    return mapping


def get_ast_script(source_a, source_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    generate_ast_script(source_a, source_b)
    with open(FILE_AST_SCRIPT, "r") as script_file:
        script_lines = script_file.readlines()
        return script_lines


def id_from_string(simplestring):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    return int(simplestring.split("(")[-1][:-1])


def clean_parse(content, separator):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if content.count(separator) == 1:
        return content.split(separator)
    i = 0
    while i < len(content):
        if content[i] == "\"":
            i += 1
            while i < len(content) - 1:
                if content[i] == "\\":
                    i += 2
                elif content[i] == "\"":
                    i += 1
                    break
                else:
                    i += 1
            prefix = content[:i]
            rest = content[i:].split(separator)
            node1 = prefix + rest[0]
            node2 = separator.join(rest[1:])
            return [node1, node2]
        i += 1
    # If all the above fails (it shouldn't), hope for some luck:
    nodes = content.split(separator)
    half = len(nodes) // 2
    node1 = separator.join(nodes[:half])
    node2 = separator.join(nodes[half:])
    return [node1, node2]


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


def diff():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.title("Locating changed functions")
    safe_exec(generate_diff, "search for changed functions")
    print(Common.DIFF_FUNCTION_LIST)
