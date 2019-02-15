#! /usr/bin/env python3
# -*- coding: utf-8 -*-



import os
import sys
from common.Tools import execute_command
from entities import Project
from common import Vault
from utilities import Output
from phases import Tracer, Builder


def load_standard_list():
    with open(Vault.FILE_STANDARD_FUNCTION_LIST, "r") as list_file:
        Vault.STANDARD_FUNCTION_LIST = [line[:-1] for line in list_file]
    with open(Vault.FILE_STANDARD_MACRO_LIST, "r") as list_file:
        Vault.STANDARD_MACRO_LIST = [line[:-1] for line in list_file]


def set_env_value():
    Output.normal("setting environment values")
    os.environ["PYTHONPATH"] = "/home/rshariffdeen/workspace/z3/build/python"
    execute_command("export PYTHONPATH=/home/rshariffdeen/workspace/z3/build/python")


def load_values():
    Vault.Project_A = Project.Project(Vault.VALUE_PATH_A, "Pa", Vault.VALUE_EXPLOIT_A)
    Vault.Project_B = Project.Project(Vault.VALUE_PATH_B, "Pb")
    Vault.Project_C = Project.Project(Vault.VALUE_PATH_C, "Pc", Vault.VALUE_EXPLOIT_C)
    Vault.Project_D = Project.Project(Vault.VALUE_PATH_C + "-patch", "Pd")
    load_standard_list()


def create_patch_dir():
    patch_dir = Vault.VALUE_PATH_C + "-patch"
    if not os.path.isdir(patch_dir):
        create_command = "cp -rf " + Vault.VALUE_PATH_C + " " + Vault.VALUE_PATH_C + "-patch"
        execute_command(create_command)


def create_output_dir():
    conf_file_name = Vault.FILE_CONFIGURATION.split("/")[-1]
    dir_name = conf_file_name.replace(".conf", "")
    Vault.DIRECTORY_OUTPUT = Vault.DIRECTORY_OUTPUT_BASE + "/" + dir_name
    if not os.path.isdir(Vault.DIRECTORY_OUTPUT):
        create_command = "mkdir " + Vault.DIRECTORY_OUTPUT
        execute_command(create_command)


def read_conf():
    Output.normal("reading configuration values")
    if len(sys.argv) > 1:
        for arg in sys.argv:
            if Vault.ARG_DEBUG in arg:
                Vault.DEBUG = True
            elif Vault.ARG_NO_BUILD in arg:
                Vault.NO_BUILD = True
            elif Vault.ARG_CONF_FILE in arg:
                Vault.FILE_CONFIGURATION = str(arg).replace(Vault.ARG_CONF_FILE, '')
            elif Vault.ARG_NO_SYM_TRACE_GEN in arg:
                Vault.NO_SYM_TRACE_GEN = True
            elif "PatchWeave.py" in arg:
                continue
            else:
                Output.error("Invalid argument: " + arg)
                Output.help()
                exit()
    else:
        Output.help()
        exit()

    if not os.path.exists(Vault.FILE_CONFIGURATION):
        Output.error("[NOT FOUND] Configuration file " + Vault.FILE_CONFIGURATION)
        exit()

    with open(Vault.FILE_CONFIGURATION, 'r') as conf_file:
        configuration_list = [i.strip() for i in conf_file.readlines()]

    for configuration in configuration_list:
        if Vault.CONF_EXPLOIT_A in configuration:
            Vault.VALUE_EXPLOIT_A = configuration.replace(Vault.CONF_EXPLOIT_A, '')
        elif Vault.CONF_EXPLOIT_C in configuration:
            Vault.VALUE_EXPLOIT_C = configuration.replace(Vault.CONF_EXPLOIT_C, '')
        elif Vault.CONF_PATH_POC in configuration:
            Vault.VALUE_PATH_POC = configuration.replace(Vault.CONF_PATH_POC, '')
        elif Vault.CONF_PATH_A in configuration:
            Vault.VALUE_PATH_A = configuration.replace(Vault.CONF_PATH_A, '')
        elif Vault.CONF_PATH_B in configuration:
            Vault.VALUE_PATH_B = configuration.replace(Vault.CONF_PATH_B, '')
        elif Vault.CONF_PATH_C in configuration:
            Vault.VALUE_PATH_C = configuration.replace(Vault.CONF_PATH_C, '')
        elif Vault.CONF_EXPLOIT_PREPARE in configuration:
            Vault.VALUE_EXPLOIT_PREPARE = configuration.replace(Vault.CONF_EXPLOIT_PREPARE, '')
        elif Vault.CONF_FLAGS_A in configuration:
            Vault.VALUE_BUILD_FLAGS_A = configuration.replace(Vault.CONF_FLAGS_A, '')
        elif Vault.CONF_FLAGS_C in configuration:
            Vault.VALUE_BUILD_FLAGS_C = configuration.replace(Vault.CONF_FLAGS_C, '')
        elif Vault.CONF_BUILD_COMMAND_A in configuration:
            Vault.VALUE_BUILD_COMMAND_A = configuration.replace(Vault.CONF_BUILD_COMMAND_A, '')
        elif Vault.CONF_BUILD_COMMAND_C in configuration:
            Vault.VALUE_BUILD_COMMAND_C = configuration.replace(Vault.CONF_BUILD_COMMAND_C, '')
        elif Vault.CONF_ASAN_FLAG in configuration:
            Vault.VALUE_ASAN_FLAG = configuration.replace(Vault.CONF_ASAN_FLAG, '')


def initialize():
    Output.title("Initializing project for Transplantation")
    Output.sub_title("loading configuration")
    read_conf()
    create_patch_dir()
    create_output_dir()
    load_values()
    Output.sub_title("set environment")
    set_env_value()
    if not Vault.NO_BUILD:
        Builder.build_asan()
        Tracer.test_exploits()
    else:
        Builder.soft_restore_all()
