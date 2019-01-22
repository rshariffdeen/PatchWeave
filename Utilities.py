# -*- coding: utf-8 -*-

import os
import sys
import subprocess
import Logger
import Output
import Common

WLLVM_EXTRACTOR = "extract-bc"

def execute_command(command, show_output=True):
    # Print executed command and execute it in console
    Output.command(command)
    command = "{ " + command + " ;} 2> " + Common.FILE_ERROR_LOG
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return str(process.returncode)


def create_directories():
    if not os.path.isdir(Common.DIRECTORY_LOG):
        os.makedirs(Common.DIRECTORY_LOG)

    if not os.path.isdir(Common.DIRECTORY_OUTPUT):
        os.makedirs(Common.DIRECTORY_OUTPUT)

    if not os.path.isdir(Common.DIRECTORY_BACKUP):
        os.makedirs(Common.DIRECTORY_BACKUP)

    if not os.path.isdir(Common.DIRECTORY_VECTORS_A):
        os.makedirs(Common.DIRECTORY_VECTORS_A)

    if not os.path.isdir(Common.DIRECTORY_VECTORS_B):
        os.makedirs(Common.DIRECTORY_VECTORS_B)

    if not os.path.isdir(Common.DIRECTORY_VECTORS_C):
        os.makedirs(Common.DIRECTORY_VECTORS_C)


def error_exit(*args):
    print("\n")
    for i in args:
        Logger.error(i)
        Output.error(i)
    raise Exception("Error. Exiting...")


def find_files(src_path, extension, output):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    # Save paths to all files in src_path with extension extension to output
    find_command = "find " + src_path + " -name '" + extension + "' > " + output
    execute_command(find_command)


def clean_files():
    # Remove other residual files stored in ./output/
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.information("Removing other residual files...")
    if os.path.isdir("output"):
        clean_command = "rm -rf " + Common.DIRECTORY_OUTPUT
        execute_command(clean_command)


def get_file_extension_list(src_path, output_file_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    extensions = set()
    find_command = "find " + src_path + " -type f -not -name '*\.c' -not -name '*\.h'" + \
        " > " + output_file_name
    execute_command(find_command)
    with open(output_file_name, 'r') as f:
        a = f.readline().strip()
        while(a):
            a = a.split("/")[-1]
            if "." in a:
                extensions.add("*." + a.split(".")[-1])
            else:
                extensions.add(a)
            a = f.readline().strip()
    return extensions


def backup_file(file_path, backup_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    backup_command = "cp " + file_path + " " + Common.DIRECTORY_BACKUP + "/" + backup_name
    execute_command(backup_command)


def restore_file(file_path, backup_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    restore_command = "cp " + Common.DIRECTORY_BACKUP + "/" + backup_name + " " + file_path
    execute_command(restore_command)


def reset_git(source_directory):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    reset_command = "cd " + source_directory + ";git reset --hard HEAD"
    execute_command(reset_command)


def extract_bitcode(binary_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    extract_command = WLLVM_EXTRACTOR + " " + binary_path
    # print(extract_command)
    execute_command(extract_command)
    return binary_directory, binary_name
