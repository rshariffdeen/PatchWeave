#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import Logger
import Emitter
import Builder
import Exploiter


def run_compilation():
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Builder.build_verify()


def compare_output(target_output, target_exit_code, repaired_target_output, repaired_target_exit_code):
    Emitter.sub_sub_title("before transplantation")
    Emitter.program_output(target_output)
    Emitter.normal("\t\t\t exit code:" + str(target_exit_code))
    Emitter.sub_sub_title("after transplantation")
    Emitter.program_output(repaired_target_output)
    Emitter.normal("\t\t\t exit code:" + str(repaired_target_exit_code))


def run_exploit(target_trace_info, exploit_command, project_path, poc_path,
                   prog_output_file, crash_word_list, crash_location):

    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())

    target_exit_code, target_crashed, target_output_file = target_trace_info
    target_output = ""
    with open(target_output_file, "r") as prev_file:
        target_output = prev_file.readlines()

    Emitter.sub_sub_title("running exploit on repaired program")
    if crash_location == "":
        Builder.build_asan()
        repaired_target_exit_code, \
        repaired_target_crashed, \
        repaired_target_output = Exploiter.run_exploit(exploit_command,
                                                                project_path,
                                                                poc_path,
                                                                prog_output_file)

    else:
        repaired_target_exit_code,\
        repaired_target_crashed, \
        repaired_target_output = Exploiter.run_exploit(exploit_command,
                                                                project_path,
                                                                poc_path,
                                                                prog_output_file)
    print(repaired_target_crashed, target_crashed)
    if target_crashed:
        if repaired_target_crashed:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.error("\n\tprogram crashed with exit code " + str(target_exit_code))
        else:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.success("\n\tprogram did not crash!!")
    else:
        runtime_error_count_c = target_output.count("runtime error")
        runtime_error_count_d = repaired_target_output.count("runtime error")

        if repaired_target_crashed:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.error("\n\tprogram crashed with exit code " + str(target_exit_code))

        if runtime_error_count_c <= runtime_error_count_d:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.error("\n\tprogram was not repaired!!")
        elif runtime_error_count_d == 0:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.error("\n\tprogram was repaired!!")
        else:
            compare_output(target_output,
                           target_exit_code,
                           repaired_target_output,
                           repaired_target_exit_code
                           )
            Emitter.success("\n\tprogram partially repaired!!")

