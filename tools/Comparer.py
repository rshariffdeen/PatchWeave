#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import Oracle


def compare_test_output(output_c, output_d):
    return_code_c, program_crashed_c, program_output_c = output_c
    return_code_d, program_crashed_d, program_output_d = output_d
    if str(program_output_c) == str(program_output_d):
        return 0
    else:
        if program_crashed_c:
            if program_crashed_d:
                if return_code_c == return_code_d:
                    return 0
                else:
                    print(program_output_c)
                    print(program_output_d)
                    return -1
            else:
                return 1

        else:
            if program_crashed_d:
                print(program_output_c)
                print(program_output_d)
                exit(1)
            else:
                if return_code_c == return_code_d:
                    return 0
                else:
                    print(program_output_c)
                    print(program_output_d)
                    return -1

