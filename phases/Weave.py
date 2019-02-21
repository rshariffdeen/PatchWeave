#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import time
from common.Utilities import error_exit
from common import Definitions, Values
import Concolic
import Analyse
import Trace
from tools import Logger, Solver, Fixer, Emitter, Weaver

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


FILE_VAR_EXPR_LOG_A = ""
FILE_VAR_EXPR_LOG_B = ""
FILE_VAR_EXPR_LOG_C = ""
FILE_VAR_MAP = ""
FILE_SKIP_LIST = ""
FILE_AST_SCRIPT = ""
FILE_TEMP_FIX = ""


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
    Weaver.weave_headers(missing_header_list)


def transplant_missing_macros():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Weaver.weave_macros(missing_macro_list)


def transplant_missing_functions():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    global missing_header_list, missing_macro_list
    missing_header_list, missing_macro_list = Weaver.weave_functions(missing_function_list)


def transplant_code():
    global missing_function_list, modified_source_list
    path_a = Values.PATH_A
    path_b = Values.PATH_B
    path_c = Values.PATH_C
    path_d = Values.Project_D.path
    sym_poc_path = Concolic.FILE_SYMBOLIC_POC
    bit_size = Concolic.VALUE_BIT_SIZE
    log_file_info = FILE_VAR_EXPR_LOG_A, FILE_VAR_EXPR_LOG_B, FILE_VAR_EXPR_LOG_C
    out_file_info = FILE_SKIP_LIST, FILE_AST_SCRIPT, FILE_VAR_MAP
    file_info = out_file_info, log_file_info
    trace_list = Trace.list_trace_c
    for diff_loc in Analyse.diff_info.keys():
        Emitter.normal(diff_loc)
        diff_loc_info = Analyse.diff_info[diff_loc]
        div_sym_path_cond = get_sym_path_cond(diff_loc)
        last_sym_path_cond = Concolic.sym_path_c[Concolic.sym_path_c.keys()[-1]]
        estimate_loc = Solver.estimate_divergent_point(div_sym_path_cond,
                                                       last_sym_path_cond,
                                                       Concolic.sym_path_c,
                                                       Trace.list_trace_c
                                                       )
        identified_modified_source_list, identified_missing_function_list = Weaver.weave_code(diff_loc,
                                                                        diff_loc_info,
                                                                        path_a,
                                                                        path_b,
                                                                        path_c,
                                                                        path_d,
                                                                        bit_size,
                                                                        sym_poc_path,
                                                                        file_info,
                                                                        trace_list,
                                                                        estimate_loc
                                                                        )
        missing_function_list = missing_function_list.update(identified_missing_function_list)
        modified_source_list = modified_source_list + identified_modified_source_list


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


def weave():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.title("Repairing vulnerability")
    set_values()
    safe_exec(transplant_code, "transplanting code")
    safe_exec(transplant_missing_functions, "transplanting functions")
    safe_exec(transplant_missing_macros, "transplanting macros")
    safe_exec(transplant_missing_header, "transplanting header files")
    safe_exec(Fixer.check, "correcting syntax errors", modified_source_list)
