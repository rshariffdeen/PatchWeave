#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import time
from tools import Emitter, Logger
from common import Definitions, Values
from common.Utilities import error_exit, create_directories
from phases import Trace, Weave, Concolic, Slice, Analyse, Verify, Initialize, Exploit


def first_run_check():
    create_directories()


def run_patchweave():
    # read configuration and check first run
    first_run_check()
    Emitter.start()
    start_time = time.time()
    time_info = dict()

    # Prepare projects directories by getting paths and cleaning residual files
    time_check = time.time()
    Initialize.initialize()
    time_info[Definitions.KEY_DURATION_INITIALIZATION] = str(time.time() - time_check)

    if not Values.ONLY_VERIFY:

        time_check = time.time()
        Exploit.exploit()
        time_info[Definitions.KEY_DURATION_EXPLOIT] = str(time.time() - time_check)

        time_check = time.time()
        Analyse.analyse()
        time_info[Definitions.KEY_DURATION_DIFF_ANALYSIS] = str(time.time() - time_check)

        time_check = time.time()
        Trace.trace()
        time_info[Definitions.KEY_DURATION_TRACE_ANALYSIS] = str(time.time() - time_check)

        time_check = time.time()
        Concolic.execute()
        time_info[Definitions.KEY_DURATION_SYMBOLIC_TRACE_ANALYSIS] = str(time.time() - time_check)

        time_check = time.time()
        Slice.slice()
        time_info[Definitions.KEY_DURATION_SLICE] = str(time.time() - time_check)

        time_check = time.time()
        Weave.weave()
        time_info[Definitions.KEY_DURATION_TRANSPLANTATION] = str(time.time() - time_check)

    time_check = time.time()
    Verify.verify()
    time_info[Definitions.KEY_DURATION_VERIFICATION] = str(time.time() - time_check)

    # Final running time and exit message
    time_info[Definitions.KEY_DURATION_TOTAL] = str(time.time() - start_time)
    Emitter.end(time_info)
    Logger.end(time_info)


if __name__ == "__main__":
    try:
        run_patchweave()
    except KeyboardInterrupt as e:
        error_exit("Program Interrupted by User")
