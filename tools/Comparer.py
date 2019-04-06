#! /usr/bin/env python3
# -*- coding: utf-8 -*-



from common import Definitions


def compare_test_output(output_a, output_b):
    if str(output_a) == str(output_b):
        return 0
    else:
        if any(crash_word in str(output_a).lower() for crash_word in Definitions.crash_word_list):
            return 1
        else:
            print(output_a)
            print(output_b)
            exit(1)
