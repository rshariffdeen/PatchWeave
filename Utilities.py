# -*- coding: utf-8 -*-

import os
import subprocess
import Logger
import Output
import Common


def execute_command(command):
    # Print executed command and execute it in console
    message = "running command " + command
    Output.command(message)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return output.decode("utf-8").strip(), error


def create_directories():
    if not os.path.isdir(Common.DIRECTORY_LOG):
        os.makedirs(Common.DIRECTORY_LOG)

    if not os.path.isdir(Common.DIRECTORY_OUTPUT):
        os.makedirs(Common.DIRECTORY_OUTPUT)


def error_exit(*args):
    print("\n")
    for i in args:
        Logger.error(i)
        Output.error(i)
    raise Exception("Error. Exiting...")


def find_files(src_path, extension, output):
    # Save paths to all files in src_path with extension extension to output
    find_command = "find " + src_path + " -name '" + extension + "' > " + output
    execute_command(find_command)


def clean_files():
    # Remove other residual files stored in ./output/
    Output.information("Removing other residual files...")
    if os.path.isdir("output"):
        clean_command = "rm -rf " + Common.DIRECTORY_OUTPUT
        execute_command(clean_command)


def get_file_extension_list(src_path, output_file_name):
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
