# -*- coding: utf-8 -*-

import os
import subprocess
import Logger
import Output
import Common


def execute_command(command):
    # Print executed command and execute it in console
    message = "running command " + command
    Logger.information(message)
    if Common.DEBUG:
        Output.information()
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
    raise Exception("Error. Exiting...")
