#! /usr/bin/env python3
# -*- coding: utf-8 -*-

Pa = None
Pb = None
Pc = None
crash_script = None

DEBUG = False

######## Directories and Files ############
DIRECTORY_LOG = "logs"
DIRECTORY_OUTPUT = "output"

MAIN_LOG_FILE = ""


######## KEY DEFINITIONS ##################

KEY_DURATION_TOTAL = 'run-time'
KEY_DURATION_INITIALIZATION = 'initialization'
KEY_DURATION_CLONE_DETECTION = 'clone-detection'
KEY_DURATION_TRANSLATION = 'translation'
KEY_DURATION_TRANSPLANTATION = "transplantation"


CONF_FILE_NAME = "crochet.conf"
PATCH_COMMAND = "crochet-patch"
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
