# -*- coding: utf-8 -*-

import sys
import Common
import Logger

GREY = '\t\x1b[1;30m'
RED = '\t\x1b[1;31m'
GREEN = '\x1b[1;32m'
YELLOW = '\t\x1b[1;33m'
BLUE = '\t\x1b[1;34m'
ROSE = '\n\t\x1b[1;35m'
CYAN = '\x1b[1;36m'
WHITE = '\t\x1b[1;37m'


def write(print_message, print_color, new_line=True):
    r = "\033[K" + print_color + str(print_message) + '\x1b[0m'
    sys.stdout.write(r)
    if new_line:
        r = "\n"
        sys.stdout.write("\n")
    else:
        r = "\033[K\r"
        sys.stdout.write(r)
    sys.stdout.flush()


def title(title):
    write("_"*100 + "\n\n\t" + title + "\n" + "_"*100+"\n", CYAN)


def sub_title(sub_title):
    write("\n\t" + sub_title + "\n\t" + "-"*90+"\n", CYAN)


def output(message, jumpline=True):
    write(message, BLUE, jumpline)


def information(message, jump_line=True):
    if not Common.DEBUG:
        write(message, GREY, jump_line)


def statistics(message):
    write(message, WHITE)


def error(message):
    write(message, RED)


def success(message):
    write(message, GREEN)


def warning(message):
    if not Common.DEBUG:
        write(message, YELLOW)

      
def initialize():
    output("\n\n" + "#"*100 + "\n\n\tStarting PatchWeave...\n\n" + "#"*100)
    Logger.initialize()


def end(time_info):
    Logger.end(time_info)
    statistics("\nRun time statistics:\n-----------------------\n")
    statistics("Initialization: " + time_info[Common.KEY_DURATION_INITIALIZATION] + " seconds")
    statistics("Clone Detection: " + time_info[Common.KEY_DURATION_CLONE_DETECTION] + " seconds")
    statistics("Translation: " + time_info[Common.KEY_DURATION_TRANSLATION] + " seconds")
    statistics("Transplantation: " + time_info[Common.KEY_DURATION_TRANSPLANTATION] + " seconds")
    success("\nPatchWeave finished successfully after " + time_info[Common.KEY_DURATION_TOTAL] + " seconds\n")


