#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from Utilities import execute_command, error_exit
import Project
import Common
import Output
import Logger

CC = ""
CXX = ""
C_FLAGS = ""
CXX_FLAGS = ""
LD_FLAGS = ""


def config_project(project_path, is_llvm):
    dir_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/configure"):
        config_command = "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=" + C_FLAGS + " "
        config_command += "CXXFLAGS=" + CXX_FLAGS

    elif os.path.exists(project_path + "/configure.ac"):
        config_command = "autoreconf -i;"
        config_command += "CC=" + CC + " "
        config_command += "CXX=" + CXX + " "
        config_command += "./configure "
        config_command += "CFLAGS=" + C_FLAGS + " "
        config_command += "CXXFLAGS=" + CXX_FLAGS

    elif os.path.exists(project_path + "/CMakeLists.txt"):
        config_command = "cmake -DCMAKE_CC=" + CC + " "
        config_command += "-DCMAKE_CXX="  + CXX + " "
        config_command += "-DCMAKE_C_FLAGS=" + C_FLAGS + " "
        config_command += "-DCMAKE_CXX_FLAGS=" + CXX_FLAGS + " . "
    if is_llvm:
        config_command = "LLVM_COMPILER=clang;" + config_command

    config_command = dir_command + config_command
    execute_command(config_command)


def build_project(project_path):
    dir_command = "cd " + project_path + ";"
    build_command = "bear make CFLAGS=" + C_FLAGS + " "
    build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + Common.FILE_MAKE_LOG
    build_command = dir_command + build_command
    execute_command(build_command)


def build_all():
    Output.normal("building")
    Output.normal("\t" + Common.Project_A.path)
    build_project(Common.Project_A.path)
    Output.normal("\t" + Common.Project_B.path)
    build_project(Common.Project_B.path)
    Output.normal("\t" + Common.Project_C.path)
    build_project(Common.Project_C.path)


def config_all(is_llvm=False):
    Output.normal("configuring projects")
    Output.normal("\t" + Common.Project_A.path)
    config_project(Common.Project_A.path, is_llvm)
    Output.normal("\t" + Common.Project_B.path)
    config_project(Common.Project_B.path, is_llvm)
    Output.normal("\t" + Common.Project_C.path)
    config_project(Common.Project_C.path, is_llvm)


def build_normal():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Output.sub_title("building projects")
    CC = "clang"
    CXX = "clang++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    build_all()


def build_asan():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Output.sub_title("building projects")
    CC = "clang"
    CXX = "clang++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=undefined'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=undefined'"
    build_all()


def build_llvm():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Output.sub_title("building projects")
    CC = "wllvm"
    CXX = "wllvm++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=undefined'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=undefined'"
    build_all()
