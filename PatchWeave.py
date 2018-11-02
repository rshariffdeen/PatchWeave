#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import time
import Output
import Common
from Utilities import error_exit, create_directories
import Initializer
import os, sys
import Differ


def first_run_check():
    create_directories()


def read_conf():
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
        elif Common.CONF_PATH_A in configuration:
            Common.VALUE_PATH_A = configuration.replace(Common.CONF_PATH_A, '')
        elif Common.CONF_PATH_B in configuration:
            Common.VALUE_PATH_B = configuration.replace(Common.CONF_PATH_B, '')
        elif Common.CONF_PATH_C in configuration:
            Common.VALUE_PATH_C = configuration.replace(Common.CONF_PATH_C, '')


def run_patchweave():
    # read configuration and check first run
    read_conf()
    first_run_check()
    Output.start()
    start_time = time.time()
    time_info = dict()

    # Prepare projects directories by getting paths and cleaning residual files
    initialization_start_time = time.time()
    Initializer.initialize()
    time_info[Common.KEY_DURATION_INITIALIZATION] = str(time.time() - initialization_start_time)

    function_identification_start_time = time.time()
    Differ.diff()
    time_info[Common.KEY_DURATION_CLONE_DETECTION] = str(time.time() - function_identification_start_time)

    patch_extraction_start_time = time.time()
    #Extraction.extract()
    patch_extraction_duration = str(time.time() - patch_extraction_start_time)

    mapping_start_time = time.time()
    #Mapping.generate()
    time_info[Common.KEY_DURATION_TRANSLATION] = str(time.time() - mapping_start_time)

    translation_start_time = time.time()
    #Translation.translate()
    translation_duration = str(time.time() - translation_start_time)

    transplantation_start_time = time.time()
    #Weaver.weave()
    time_info[Common.KEY_DURATION_TRANSPLANTATION] = str(time.time() - transplantation_start_time)

    # Final clean
    #Logger.title("Cleaning residual files generated by Crochet...")

    # Final running time and exit message
    time_info[Common.KEY_DURATION_TOTAL] = str(time.time() - start_time)
    Output.end(time_info)


if __name__ == "__main__":
    try:
        run_patchweave()
    except KeyboardInterrupt as e:
        error_exit("Program Interrupted by User")
