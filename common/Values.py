#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

Project_A = None
Project_B = None
Project_C = None
Project_D = None

DEBUG = False
NO_BUILD = False
NO_SYM_TRACE_GEN = False

STANDARD_FUNCTION_LIST = list()
STANDARD_MACRO_LIST = list()

PROJECT_A_FUNCTION_LIST = ""
PROJECT_B_FUNCTION_LIST = ""
PROJECT_C_FUNCTION_LIST = ""
DIFF_FUNCTION_LIST = ""
DIFF_LINE_LIST = dict()
DIVERGENT_POINT_LIST = list()
FUNCTION_MAP = ""
CRASH_LINE_LIST = dict()
TRACE_LIST = dict()


# ------------------ Configuration Values ---------------
PATH_A = ""
PATH_B = ""
PATH_C = ""
EXPLOIT_A = ""
EXPLOIT_C = ""
BUILD_FLAGS_A = ""
BUILD_FLAGS_C = ""
BUILD_COMMAND_A = ""
BUILD_COMMAND_C = ""
PATH_POC = ""
EXPLOIT_PREPARE = ""
ASAN_FLAG = ""


header_file_list_to_patch = []
c_file_list_to_patch = []

generated_script_for_header_files = dict()
generated_script_for_c_files = dict()

translated_script_for_files = dict()
variable_map = dict()
