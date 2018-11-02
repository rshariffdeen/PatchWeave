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
    Logger.information(title)


def sub_title(subtitle):
    write("\n\t" + subtitle + "\n\t" + "-"*90+"\n", CYAN)
    Logger.information(subtitle)


def command(message):
    if Common.DEBUG:
        message = "running command\n\t" + message
        write(message, ROSE)
    Logger.command(message)


def normal(message, jump_line=True):
    write(message, BLUE, jump_line)
    # Logger.output(message)


def information(message, jump_line=True):
    if Common.DEBUG:
        write(message, GREY, jump_line)
    Logger.information(message)


def statistics(message):
    write(message, WHITE)
    Logger.output(message)


def error(message):
    write(message, RED)
    Logger.error(message)


def success(message):
    write(message, GREEN)
    Logger.output(message)


def warning(message):
    if Common.DEBUG:
        write(message, YELLOW)
    Logger.warning(message)


def start():
    Logger.create()
    write("\n\n" + "#"*100 + "\n\n\tPatchWeave - Automated Patch Transplantation\n\n" + "#"*100, BLUE)


def end(time_info):
    Logger.end(time_info)
    statistics("\nRun time statistics:\n-----------------------\n")
    statistics("Initialization: " + time_info[Common.KEY_DURATION_INITIALIZATION] + " seconds")
    statistics("Clone Detection: " + time_info[Common.KEY_DURATION_CLONE_DETECTION] + " seconds")
    statistics("Translation: " + time_info[Common.KEY_DURATION_TRANSLATION] + " seconds")
    statistics("Transplantation: " + time_info[Common.KEY_DURATION_TRANSPLANTATION] + " seconds")
    success("\nPatchWeave finished successfully after " + time_info[Common.KEY_DURATION_TOTAL] + " seconds\n")


def help():
    print("Usage: python patchweave [OPTIONS] " + Common.ARG_CONF_FILE + "$FILE_PATH")
    print("Options are:")
    print("\t" + Common.ARG_DEBUG + "\t| " + "enable debugging information")


