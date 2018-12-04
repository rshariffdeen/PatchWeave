#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from Utilities import execute_command, error_exit
import Project
import Common
import Output
import Logger


def load_values():
    Common.Project_A = Project.Project(Common.VALUE_PATH_A, "Pa", Common.VALUE_EXPLOIT_A)
    Common.Project_B = Project.Project(Common.VALUE_PATH_B, "Pb")
    Common.Project_C = Project.Project(Common.VALUE_PATH_C, "Pc", Common.VALUE_EXPLOIT_C)


def make_clean(project_path):
    Output.normal("\tremoving binaries and make files")
    clean_command = "cd " + project_path + "; make clean; make distclean"
    execute_command(clean_command)


def restore_modifications(project_path):
    Output.normal("\trestoring modified files")
    restore_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/.git"):
        restore_command += "git clean -fd; git reset --hard HEAD"
    elif os.path.exists(project_path + "/.svn"):
        restore_command += "svn revert -R .; svn status --no-ignore | grep '^\?' | sed 's/^\?     //'  | xargs rm -rf"
    execute_command(restore_command)


def clean_projects():
    Output.normal(Common.Project_A.path)
    make_clean(Common.Project_A.path)
    restore_modifications(Common.Project_A.path)

    Output.normal(Common.Project_B.path)
    make_clean(Common.Project_B.path)
    restore_modifications(Common.Project_B.path)

    Output.normal(Common.Project_C.path)
    make_clean(Common.Project_C.path)
    restore_modifications(Common.Project_C.path)


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
        elif Common.CONF_BUILD_A in configuration:
            Common.VALUE_BUILD_SCRIPT_PATH_A = configuration.replace(Common.CONF_BUILD_A, '')
        elif Common.CONF_BUILD_B in configuration:
            Common.VALUE_BUILD_SCRIPT_PATH_A = configuration.replace(Common.CONF_BUILD_B, '')
        elif Common.CONF_BUILD_C in configuration:
            Common.VALUE_BUILD_SCRIPT_PATH_C = configuration.replace(Common.CONF_BUILD_C, '')


def initialize():
    Output.title("Initializing project for Transplantation")
    Output.sub_title("loading configuration")
    read_conf()
    load_values()
    Output.sub_title("cleaning residue files")
    # clean_projects()
