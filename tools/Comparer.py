#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import os
import Emitter
import Logger


def compare_test_output(output_a, output_b):
    if str(output_a) == str(output_b):
        return True
    else:
        print(output_a)
        print(output_b)
        exit(1)
