#! /usr/bin/env python3
# -*- coding: utf-8 -*-



from common import Definitions
import Oracle


def compare_test_output(output_a, output_b):
    if str(output_a) == str(output_b):
        return 0
    else:
        if Oracle.did_program_crash(output_a):
            if Oracle.did_program_crash(output_b):
                print(output_b)
                print(output_a)
                return 0
            else:
                return 1

        else:
            if Oracle.did_program_crash(output_b):
                print(output_a)
                print(output_b)
                exit(1)
            else:
                print(output_b)
                print(output_a)
                return 0

