#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os

Project_A = None
Project_B = None
Project_C = None
DEBUG = False

# ------------------- Directories --------------------

DIRECTORY_MAIN = os.getcwd()
DIRECTORY_LOG = DIRECTORY_MAIN + "/logs"
DIRECTORY_OUTPUT = DIRECTORY_MAIN + "/output"
DIRECTORY_BACKUP = DIRECTORY_MAIN + "/backup"

# ------------------- Files --------------------

FILE_MAIN_LOG = ""
FILE_LAST_LOG = DIRECTORY_LOG + "/log-latest"
FILE_CONFIGURATION = ""



# ------------------- Configuration --------------------

CONF_PATH_A = "path_a:"
CONF_PATH_B = "path_b:"
CONF_PATH_C = "path_c:"
CONF_EXPLOIT_A = "exploit_a"
CONF_EXPLOIT_C = "exploit_c"

# ------------------ Configuration Values ---------------
VALUE_PATH_A = ""
VALUE_PATH_B = ""
VALUE_PATH_C = ""
VALUE_EXPLOIT_A = ""
VALUE_EXPLOIT_C = ""

# ----------------- KEY DEFINITIONS -------------------

KEY_DURATION_TOTAL = 'run-time'
KEY_DURATION_INITIALIZATION = 'initialization'
KEY_DURATION_CLONE_DETECTION = 'clone-detection'
KEY_DURATION_TRANSLATION = 'translation'
KEY_DURATION_TRANSPLANTATION = "transplantation"

ARG_CONF_FILE = "--conf="
ARG_DEBUG = "--debug"


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
