#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, extract_bitcode
import Output
import Common
import Logger
import Differ
import Builder
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Generator
import Tracer
import Weaver

FILE_SYNTAX_ERRORS = Common.DIRECTORY_OUTPUT + "/syntax-errors"


def verify_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())


def verify_exploit():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())


def fix_return_type(source_location):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tfixing return type")
    print(source_location)


def fix_syntax_errors(source_file):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tfixing syntax errors")
    with open(FILE_SYNTAX_ERRORS, 'r') as error_log:
        read_line = error_log.readline()
        source_location = read_line.split(": ")[0]
        error_type = (read_line.split(" [")[-1]).replace("]", "")
        if "return-type" in error_type:
            fix_return_type(source_location)


def check_syntax_errors():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    for source_file in Weaver.modified_source_list:
        Output.normal(source_file)
        check_command = "clang-check -analyze " + source_file + " > " + FILE_SYNTAX_ERRORS
        check_command += " 2>&1"
        ret_code = execute_command(check_command)
        if ret_code != 0:
            fix_syntax_errors(source_file)
        else:
            Output.normal("\tno syntax errors")

def check():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.sub_title("checking syntax errors")
    check_syntax_errors()