#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
from common.Utilities import error_exit
import Logger
import Emitter
import Builder
import Exploiter


def run_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Builder.build_verify()


def run_exploit(prev_exit_code, exploit_command, project_path, poc_path,
                   prog_output_file, crash_word_list, crash_location):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    if crash_location == "":
        Builder.build_asan()
        target_exit_code, target_crashed, target_output = Exploiter.run_exploit(exploit_command,
                                                                project_path,
                                                                poc_path,
                                                                prog_output_file)

        if any(crash_word in target_output.lower() for crash_word in crash_word_list):
            target_crashed = True
            Emitter.normal("\tprogram crashed with exit code " + str(target_exit_code))
        else:
            if target_exit_code != 0:
                Emitter.normal("\tprogram exited with exit code " + str(target_exit_code))
            else:
                error_exit("program did not crash!!")

    else:
        target_exit_code, target_crashed, target_output = Exploiter.run_exploit(exploit_command,
                                                                project_path,
                                                                poc_path,
                                                                prog_output_file)
        if int(target_exit_code) == int(prev_exit_code):
            error_exit("\tprogram crashed with exit code " + str(target_exit_code))
        else:
            Emitter.normal("\tprogram did not crash!!")
            Emitter.normal("\t\tbefore transplantation exit code " + str(prev_exit_code))
            Emitter.normal("\t\tafter transplantation exit code " + str(target_exit_code))
