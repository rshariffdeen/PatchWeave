#! /usr/bin/env python3
# -*- coding: utf-8 -*-



import os
import sys
from Utilities import execute_command, error_exit
import Project
import Common
import Output
import Logger
from Builder import build_normal


def set_env_value():
    Output.normal("setting environment values")
    os.environ["PYTHONPATH"] = "/home/rshariffdeen/workspace/z3/build/python"
    execute_command("export PYTHONPATH=/home/rshariffdeen/workspace/z3/build/python")


def load_values():
    Common.Project_A = Project.Project(Common.VALUE_PATH_A, "Pa", Common.VALUE_EXPLOIT_A)
    Common.Project_B = Project.Project(Common.VALUE_PATH_B, "Pb")
    Common.Project_C = Project.Project(Common.VALUE_PATH_C, "Pc", Common.VALUE_EXPLOIT_C)


def read_conf():
    Output.normal("reading configuration values")
    if len(sys.argv) > 1:
        for arg in sys.argv:
            if Common.ARG_DEBUG in arg:
                Common.DEBUG = True
            elif Common.ARG_CONF_FILE in arg:
                Common.FILE_CONFIGURATION = str(arg).replace(Common.ARG_CONF_FILE, '')
    else:
        Output.help()
        exit()

    if not os.path.exists(Common.FILE_CONFIGURATION):
        Output.error("[NOT FOUND] Configuration file " + Common.FILE_CONFIGURATION)
        exit()

    with open(Common.FILE_CONFIGURATION, 'r') as conf_file:
        configuration_list = [i.strip() for i in conf_file.readlines()]

    for configuration in configuration_list:
        if Common.CONF_EXPLOIT_A in configuration:
            Common.VALUE_EXPLOIT_A = configuration.replace(Common.CONF_EXPLOIT_A, '')
        elif Common.CONF_EXPLOIT_C in configuration:
            Common.VALUE_EXPLOIT_C = configuration.replace(Common.CONF_EXPLOIT_C, '')
        elif Common.CONF_PATH_POC in configuration:
            Common.VALUE_PATH_POC = configuration.replace(Common.CONF_PATH_POC, '')
        elif Common.CONF_PATH_A in configuration:
            Common.VALUE_PATH_A = configuration.replace(Common.CONF_PATH_A, '')
        elif Common.CONF_PATH_B in configuration:
            Common.VALUE_PATH_B = configuration.replace(Common.CONF_PATH_B, '')
        elif Common.CONF_PATH_C in configuration:
            Common.VALUE_PATH_C = configuration.replace(Common.CONF_PATH_C, '')
        elif Common.CONF_EXPLOIT_PREPARE in configuration:
            Common.VALUE_EXPLOIT_PREPARE = configuration.replace(Common.CONF_EXPLOIT_PREPARE, '')
        elif Common.CONF_FLAGS_A in configuration:
            Common.VALUE_BUILD_FLAGS_A = configuration.replace(Common.CONF_FLAGS_A, '')
        elif Common.CONF_FLAGS_B in configuration:
            Common.VALUE_BUILD_FLAGS_B = configuration.replace(Common.CONF_FLAGS_B, '')
        elif Common.CONF_FLAGS_C in configuration:
            Common.VALUE_BUILD_FLAGS_C = configuration.replace(Common.CONF_FLAGS_C, '')


def initialize():
    Output.title("Initializing project for Transplantation")
    Output.sub_title("loading configuration")
    read_conf()
    load_values()
    Output.sub_title("set environment")
    set_env_value()
    Output.sub_title("cleaning residue files")
    #build_normal()
