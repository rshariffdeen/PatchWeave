#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from Utilities import error_exit
import Project
import Common
import Output


def initialize():
    Output.title("Initializing project for Transplantation")
    Project.Project(Common.VALUE_PATH_A, "Pa", Common.VALUE_EXPLOIT_A)
    Project.Project(Common.VALUE_PATH_B, "Pb")
    Project.Project(Common.VALUE_PATH_C, "Pc", Common.VALUE_EXPLOIT_C)
