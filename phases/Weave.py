#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from common.Utilities import execute_command, error_exit, backup_file, show_partial_diff, get_code
from common import Definitions, Values
import Concolic
from ast import ASTGenerator
import Analyse
import Trace
from tools import Mapper, Identifier, KleeExecutor, Logger, Solver, Fixer, Emitter, Writer, Weaver

function_list_a = list()
function_list_b = list()
function_list_c = list()
target_candidate_function_list = list()
mapping_ba = dict()
missing_function_list = dict()
missing_macro_list = dict()
missing_header_list = dict()

modified_source_list = list()

var_expr_map_a = dict()
var_expr_map_b = dict()
var_expr_map_c = dict()

ast_map_a = dict()
ast_map_b = dict()
ast_map_c = dict()

TOOL_AST_PATCH = "patchweave"

FILE_VAR_EXPR_LOG_A = ""
FILE_VAR_EXPR_LOG_B = ""
FILE_VAR_EXPR_LOG_C = ""
FILE_VAR_MAP = ""
FILE_SKIP_LIST = ""
FILE_AST_SCRIPT = ""
FILE_TEMP_FIX = ""

FILENAME_BACKUP = "temp-source"


def get_sym_path_cond(source_location):
    sym_path_cond = ""
    if Values.PATH_A in source_location:
        for path in Trace.list_trace_a:
            if path in Concolic.sym_path_a.keys():
                sym_path_cond = Concolic.sym_path_a[path]
            if path == source_location:
                break
    elif Values.PATH_B in source_location:
        for path in Trace.list_trace_b:
            if path in Concolic.sym_path_b.keys():
                sym_path_cond = Concolic.sym_path_b[path]
            if path == source_location:
                break
    elif Values.PATH_A in source_location:
        for path in Trace.list_trace_c:
            if path in Concolic.sym_path_c.keys():
                sym_path_cond = Concolic.sym_path_c[path]
            if path == source_location:
                break
    return sym_path_cond


def transplant_missing_header():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.sub_title("transplanting missing header")
    Weaver.weave_headers(missing_header_list)


def transplant_missing_macros():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.sub_title("transplanting missing macros")
    Weaver.weave_macros(missing_macro_list)


def transplant_missing_functions():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global def_insert_point, missing_header_list
    Emitter.sub_title("transplanting missing functions")
    Weaver.weave_functions(missing_function_list)


def transplant_code():
    global mapping_ba, var_expr_map_a, var_expr_map_b, var_expr_map_c
    global ast_map_a, ast_map_b, ast_map_c
    path_a = Values.PATH_A
    path_b = Values.PATH_B
    log_file_info = FILE_VAR_EXPR_LOG_A, FILE_VAR_EXPR_LOG_B, FILE_VAR_EXPR_LOG_C
    file_info = FILE_SKIP_LIST, log_file_info
    trace_list = Trace.list_trace_c
    for diff_loc in Analyse.diff_info.keys():
        Emitter.normal(diff_loc)
        diff_loc_info = Analyse.diff_info[diff_loc]
        div_sym_path_cond = get_sym_path_cond(diff_loc)
        last_sym_path_cond = Concolic.sym_path_c[Concolic.sym_path_c.keys()[-1]]
        bytes_a = Mapper.get_input_bytes_used(div_sym_path_cond)
        bytes_c = Mapper.get_input_bytes_used(last_sym_path_cond)
        byte_list = Solver.compute_common_bytes(bytes_a, bytes_c)
        estimate_loc = Identifier.identify_divergent_point(byte_list)
        Weaver.weave_code(diff_loc,
                          diff_loc_info,
                          path_a,
                          path_b,
                          file_info,
                          trace_list,
                          estimate_loc
                          )


def transplant_patch():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for diff_loc in Analyse.diff_info.keys():
        Emitter.normal(diff_loc)
        diff_info = Analyse.diff_info[diff_loc]
        transplant_code(diff_info, diff_loc)
    transplant_missing_functions()
    transplant_missing_macros()
    transplant_missing_header()
    Fixer.check()


def safe_exec(function_def, title, *args):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_time = time.time()
    Emitter.sub_title(title + "...")
    description = title[0].lower() + title[1:]
    try:
        Logger.information("running " + str(function_def))
        if not args:
            result = function_def()
        else:
            result = function_def(*args)
        duration = str(time.time() - start_time)
        Emitter.success("\n\tSuccessful " + description + ", after " + duration + " seconds.")
    except Exception as exception:
        duration = str(time.time() - start_time)
        Emitter.error("Crash during " + description + ", after " + duration + " seconds.")
        error_exit(exception, "Unexpected error during " + description + ".")
    return result


def set_values():
    global FILE_VAR_EXPR_LOG_A, FILE_VAR_EXPR_LOG_B, FILE_VAR_EXPR_LOG_C
    global FILE_VAR_MAP, FILE_SKIP_LIST, FILE_AST_SCRIPT
    global FILE_TEMP_FIX, FILE_MACRO_DEF

    FILE_VAR_EXPR_LOG_A = Definitions.DIRECTORY_OUTPUT + "/log-sym-expr-a"
    FILE_VAR_EXPR_LOG_B = Definitions.DIRECTORY_OUTPUT + "/log-sym-expr-b"
    FILE_VAR_EXPR_LOG_C = Definitions.DIRECTORY_OUTPUT + "/log-sym-expr-c"
    FILE_VAR_MAP = Definitions.DIRECTORY_OUTPUT + "/var-map"
    FILE_SKIP_LIST = Definitions.DIRECTORY_OUTPUT + "/skip-list"
    FILE_AST_SCRIPT = Definitions.DIRECTORY_OUTPUT + "/gen-ast-script"
    FILE_TEMP_FIX = Definitions.DIRECTORY_OUTPUT + "/temp-fix"


def weave():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("repairing bug")
    set_values()
    safe_exec(transplant_code, "transplanting code")
    safe_exec(transplant_missing_functions, "transplanting functions")
    safe_exec(transplant_missing_macros, "transplanting macros")
    safe_exec(transplant_missing_header, "transplanting header files")
    safe_exec(Fixer.check(), "correcting syntax errors")
