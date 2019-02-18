#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
from phases import Trace, Concolic
import Logger
import Mapper
import Emitter
import Extractor
import Identifier


def estimate_divergent_point(path_cond_a, path_cond_b):
    Emitter.sub_sub_title("estimating divergent point in Pc")
    Emitter.normal("\textracting input bytes from div point in Pa")
    bytes_a = Extractor.extract_input_bytes_used(path_cond_a)
    Emitter.normal("\textracting input bytes from last path condition in Pc")
    bytes_c = Extractor.extract_input_bytes_used(path_cond_b)
    # print(bytes_c)
    byte_list = Extractor.extract_common_bytes(bytes_a, bytes_c)
    # print(byte_list)
    Emitter.normal("\testimating divergent point")
    estimate_loc = Identifier.identify_divergent_point(byte_list,
                                                       Concolic.sym_path_c,
                                                       Trace.list_trace_c
                                                       )
    Emitter.special("\testimated divergent point:" + estimate_loc)
    return estimate_loc


def get_best_insertion_point(insertion_point_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    return insertion_point_list[0]
