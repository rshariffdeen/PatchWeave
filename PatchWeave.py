#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import time
import Output
import Common
from Utilities import error_exit, create_directories
import Initializer
import os, sys
import Tracer
import Builder
import Differ
import Concolic
import Weaver


def first_run_check():
    create_directories()


def run_patchweave():
    # read configuration and check first run
    first_run_check()
    Output.start()
    start_time = time.time()
    time_info = dict()

    # Prepare projects directories by getting paths and cleaning residual files
    time_check = time.time()
    Initializer.initialize()
    time_info[Common.KEY_DURATION_INITIALIZATION] = str(time.time() - time_check)

    time_check = time.time()
    if not Common.NO_BUILD:
        Builder.build_llvm()
    else:
        Builder.soft_restore_all()
    time_info[Common.KEY_DURATION_BUILD] = str(time.time() - time_check)

    time_check = time.time()
    Differ.diff()
    time_info[Common.KEY_DURATION_DIFF_ANALYSIS] = str(time.time() - time_check)

    time_check = time.time()
    Tracer.trace()
    time_info[Common.KEY_DURATION_TRACE_ANALYSIS] = str(time.time() - time_check)

    time_check = time.time()
    Concolic.execute()
    time_info[Common.KEY_DURATION_SYMBOLIC_TRACE_ANALYSIS] = str(time.time() - time_check)

    time_check = time.time()
    Weaver.weave()
    time_info[Common.KEY_DURATION_TRANSPLANTATION] = str(time.time() - time_check)

    # Final running time and exit message
    time_info[Common.KEY_DURATION_TOTAL] = str(time.time() - start_time)
    Output.end(time_info)


if __name__ == "__main__":
    try:
        run_patchweave()
    except KeyboardInterrupt as e:
        error_exit("Program Interrupted by User")
