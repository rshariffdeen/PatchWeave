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

PROJECT_A_FUNCTION_LIST = ""
PROJECT_B_FUNCTION_LIST = ""
PROJECT_C_FUNCTION_LIST = ""
DIFF_FUNCTION_LIST = ""
DIFF_LINE_LIST = dict()
DIVERGENT_POINT_LIST = list()
FUNCTION_MAP = ""
CRASH_LINE_LIST = dict()
TRACE_LIST = dict()

# ------------------- Directories --------------------

DIRECTORY_MAIN = os.getcwd()
DIRECTORY_LOG = DIRECTORY_MAIN + "/logs"
DIRECTORY_OUTPUT = DIRECTORY_MAIN + "/output"
DIRECTORY_BACKUP = DIRECTORY_MAIN + "/backup"
DIRECTORY_VECTORS_A = DIRECTORY_OUTPUT + "/vectors-a"
DIRECTORY_VECTORS_B = DIRECTORY_OUTPUT + "/vectors-b"
DIRECTORY_VECTORS_C = DIRECTORY_OUTPUT + "/vectors-c"
DIRECTORY_TOOLS = DIRECTORY_MAIN + "/tools"

# ------------------- Files --------------------

FILE_MAIN_LOG = ""
FILE_ERROR_LOG = DIRECTORY_LOG + "/log-error"
FILE_LAST_LOG = DIRECTORY_LOG + "/log-latest"
FILE_MAKE_LOG = DIRECTORY_LOG + "/log-make"
FILE_CONFIGURATION = ""



# ------------------- Configuration --------------------

CONF_PATH_A = "path_a:"
CONF_PATH_B = "path_b:"
CONF_PATH_C = "path_c:"
CONF_EXPLOIT_A = "exploit_command_a:"
CONF_BUILD_COMMAND_A = "build_command_a:"
CONF_EXPLOIT_C = "exploit_command_c:"
CONF_BUILD_COMMAND_C = "build_command_c:"
CONF_FLAGS_A = "build_flags_a:"
CONF_FLAGS_C = "build_flags_c:"
CONF_PATH_POC = "path_poc:"
CONF_EXPLOIT_PREPARE = "pre_exploit:"

# ------------------ Configuration Values ---------------
VALUE_PATH_A = ""
VALUE_PATH_B = ""
VALUE_PATH_C = ""
VALUE_EXPLOIT_A = ""
VALUE_EXPLOIT_C = ""
VALUE_BUILD_FLAGS_A = ""
VALUE_BUILD_FLAGS_C = ""
VALUE_BUILD_COMMAND_A = ""
VALUE_BUILD_COMMAND_C = ""
VALUE_PATH_POC = ""
VALUE_EXPLOIT_PREPARE = ""

# ----------------- KEY DEFINITIONS -------------------

KEY_DURATION_TOTAL = 'run-time'
KEY_DURATION_INITIALIZATION = 'initialization'
KEY_DURATION_DIFF_ANALYSIS = 'diff-analysis'
KEY_DURATION_TRACE_ANALYSIS = "trace-analysis"
KEY_DURATION_SYMBOLIC_TRACE_ANALYSIS = "sym-trace-analysis"
KEY_DURATION_FUNCTION_MATCH = "match-functions"
KEY_DURATION_VARIABLE_MATCH = "match-variables"
KEY_DURATION_TRANSLATION = 'translation'
KEY_DURATION_TRANSPLANTATION = "transplantation"
KEY_DURATION_VERIFICATION = 'verification'
KEY_DURATION_BUILD = 'build-project'


# ---------------- ARGUMENTS ---------------------------
ARG_CONF_FILE = "--conf="
ARG_DEBUG = "--debug"
ARG_NO_SYM_TRACE_GEN = "--no-sym-trace-gen"
ARG_NO_BUILD = "--no-build"

# ----------------- TOOLS --------------------------------
TOOL_VECGEN = "tools/deckard/cvecgen_fail "
TOOL_VECGEN_ORIG = "tools/deckard/cvecgen "

PATCH_COMMAND = "patchweave-patch"
PATCH_SIZE = "1000"
DIFF_COMMAND = "crochet-diff "
DIFF_SIZE = "1000"
SYNTAX_CHECK_COMMAND = "clang-check "
STYLE_FORMAT_COMMAND = "clang-format -style=LLVM "


header_file_list_to_patch = []
c_file_list_to_patch = []

generated_script_for_header_files = dict()
generated_script_for_c_files = dict()

translated_script_for_files = dict()
variable_map = dict()
