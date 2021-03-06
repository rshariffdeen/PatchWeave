#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys
import Logger
import Emitter
import Extractor
import Identifier


def estimate_divergent_point(path_cond_a, path_cond_b, target_sym_path, target_trace, stack_info):
    Emitter.sub_sub_title("estimating divergent point in Pc")
    Emitter.normal("\textracting input bytes from div point in Pa")
    # print(path_cond_a)
    # print("------------")
    # print(path_cond_b)
    if path_cond_a == "":
        return None, 0
    bytes_a = Extractor.extract_input_bytes_used(path_cond_a)
    Emitter.highlight("\tdiv loc byte list:")
    print("\t\t" + str(bytes_a))
    Emitter.normal("\textracting input bytes from last path condition in Pc")
    bytes_c = Extractor.extract_input_bytes_used(path_cond_b)
    Emitter.highlight("\tlast sym-path byte list:")
    print("\t\t" + str(bytes_c))
    byte_list = Extractor.extract_common_bytes(bytes_a, bytes_c)
    Emitter.highlight("\tcommon byte list:")
    print("\t\t" + str(byte_list))
    Emitter.normal("\testimating divergent point")
    estimate_loc, count_instant = Identifier.identify_divergent_point(byte_list,
                                                       target_sym_path,
                                                       target_trace,
                                                       stack_info
                                                       )
    Emitter.highlight("\testimated divergent point:" + estimate_loc + "," + str(count_instant))
    Logger.information("\testimated divergent point:" + estimate_loc + "," + str(count_instant))
    return estimate_loc, count_instant


# Christopher P. Matthews
# christophermatthews1985@gmail.com
# Sacramento, CA, USA

def levenshtein_distance(s, t):
    ''' From Wikipedia article; Iterative with two matrix rows. '''
    if s == t:
        return 0
    elif len(s) == 0:
        return len(t)
    elif len(t) == 0:
        return len(s)
    v0 = [None] * (len(t) + 1)
    v1 = [None] * (len(t) + 1)
    for i in range(len(v0)):
        v0[i] = i
    for i in range(len(s)):
        v1[0] = i + 1
        for j in range(len(t)):
            cost = 0 if s[i] == t[j] else 1
            v1[j + 1] = min(v1[j] + 1, v0[j + 1] + 1, v0[j] + cost)
        for j in range(len(v0)):
            v0[j] = v1[j]

    return v1[len(t)]


def get_best_insertion_point(insertion_point_list):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    return insertion_point_list[0]
