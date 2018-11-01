# -*- coding: utf-8 -*-

import sys
import time
import datetime
import os
import Common


def initialize():
    log_file_name = "log-" + str(time.time())
    log_file_path = Common.DIRECTORY_LOG + "/" + log_file_name
    Common.MAIN_LOG_FILE = log_file_path
    with open(Common.MAIN_LOG_FILE, 'w+') as log_file:
        log_file.write("[Start] PatchWeave started at " + str(datetime.datetime.now()) + "\n")


def log(log_message):
    with open(Common.MAIN_LOG_FILE, 'a') as log_file:
        log_file.write(log_message)


def information(message):
    message = "[INFO]" + message + "\n";
    log(message)


def error(message):
    message = "[ERROR]" + message + "\n";
    log(message)


def output(message):
    log(message)


def warning(message):
    message = "[WARNING]" + message + "\n";
    log(message)


def end(time_duration):
    output("[END] PatchWeave ended at " + str(datetime.datetime.now()) + "\n\n")
    output("\nTime duration\n----------------------\n\n")
    output("Initialization: " + time_duration[Common.KEY_DURATION_INITIALIZATION] + " seconds\n")
    output("Clone Detection: " + time_duration[Common.KEY_DURATION_CLONE_DETECTION] + " seconds\n")
    output("Translation: " + time_duration[Common.KEY_DURATION_TRANSLATION] + " seconds\n")
    output("Transplantation: " + time_duration[Common.KEY_DURATION_TRANSPLANTATION] + " seconds\n")
    output("\nPatchWeave finished successfully after " + time_duration[Common.KEY_DURATION_TOTAL] + " seconds\n")

