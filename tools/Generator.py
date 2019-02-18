#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common import Values
from common.Utilities import backup_file, restore_file, reset_git
from tools import Logger, Emitter, Instrumentor, Builder, Extractor, KleeExecutor


def generate_symbolic_expressions(source_path, start_line, end_line,
                                  output_log, only_in_range=True):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    if Values.PATH_A in source_path:
        binary_path = Values.PATH_A + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
    elif Values.PATH_B in source_path:
        binary_path = Values.PATH_B + Values.EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_A.split(" ")[1:])
    elif Values.PATH_C in source_path:
        binary_path = Values.PATH_C + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])
    else:
        binary_path = Values.Project_D.path + Values.EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Values.EXPLOIT_C.split(" ")[1:])

    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    backup_file(binary_path, "original-bitcode")
    Instrumentor.instrument_klee_var_expr(source_path, start_line, end_line, only_in_range)
    Builder.build_instrumented_code(source_directory)
    Extractor.extract_bitcode(binary_path)
    KleeExecutor.generate_var_expressions(binary_args, binary_directory, binary_name, output_log)
    restore_file("original-bitcode", binary_path)
    reset_git(source_directory)
