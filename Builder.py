#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from Utilities import execute_command, error_exit
import Project
import Common
import Output
import Logger

CC = "clang"
CXX = "clang++"
C_FLAGS = "-g -O0 -ftrapv -fPIC"
CXX_FLAGS = "-g -O0 -ftrapv -fPIC"
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
    ret_code = execute_command(config_command)
    if int(ret_code) != 0:
        Output.error(config_command)
        error_exit("CONFIGURATION FAILED!!\nExit Code: " + str(ret_code))


def build_project(project_path, build_command=None):
    dir_command = "cd " + project_path + ";"
    if build_command is None:
        build_command = "bear make CFLAGS=" + C_FLAGS + " "
        build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + Common.FILE_MAKE_LOG
    build_command = dir_command + build_command
    # print(build_command)
    ret_code = execute_command(build_command)
    if int(ret_code) != 0:
        Output.error(build_command)
        error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))


def build_all():
    Output.normal("building")

    Output.normal("\t" + Common.Project_A.path)
    if not Common.VALUE_BUILD_COMMAND_A:
        build_project(Common.Project_A.path)
    else:
        build_project(Common.Project_A.path, Common.VALUE_BUILD_COMMAND_A)

    Output.normal("\t" + Common.Project_B.path)
    if not Common.VALUE_BUILD_COMMAND_A:
        build_project(Common.Project_B.path)
    else:
        build_project(Common.Project_B.path, Common.VALUE_BUILD_COMMAND_A)

    Output.normal("\t" + Common.Project_C.path)
    if not Common.VALUE_BUILD_COMMAND_C:
        build_project(Common.Project_C.path)
    else:
        build_project(Common.Project_C.path, Common.VALUE_BUILD_COMMAND_C)

    Output.normal("\t" + Common.Project_D.path)
    if not Common.VALUE_BUILD_COMMAND_C:
        build_project(Common.Project_D.path)
    else:
        build_project(Common.Project_D.path, Common.VALUE_BUILD_COMMAND_C)


def config_all(is_llvm=False):
    Output.normal("configuring projects")

    Output.normal("\t" + Common.Project_A.path)
    if not Common.VALUE_BUILD_COMMAND_A:
        config_project(Common.Project_A.path, is_llvm)

    Output.normal("\t" + Common.Project_B.path)
    if not Common.VALUE_BUILD_COMMAND_A:
        config_project(Common.Project_B.path, is_llvm)

    Output.normal("\t" + Common.Project_C.path)
    if not Common.VALUE_BUILD_COMMAND_C:
        config_project(Common.Project_C.path, is_llvm)

    Output.normal("\t" + Common.Project_D.path)
    if not Common.VALUE_BUILD_COMMAND_C:
        config_project(Common.Project_D.path, is_llvm)


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
    Output.sub_title("building projects with asan")
    clean_all()
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
    Output.sub_title("building projects with wllvm")
    clean_all()
    os.environ["LLVM_COMPILER"] = "clang"
    CC = "wllvm"
    CXX = "wllvm++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -ftrapv -L/home/rshariffdeen/workspace/klee/build-rshariffdeen/lib -lkleeRuntest'"
    build_all()


def restore_project(project_path):
    restore_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/.git"):
        restore_command += "git clean -fd; git reset --hard HEAD"
    elif os.path.exists(project_path + "/.svn"):
        restore_command += "svn revert -R .; svn status --no-ignore | grep '^\?' | sed 's/^\?     //'  | xargs rm -rf"
    # print(restore_command)
    execute_command(restore_command)


def soft_restore_project(project_path):
    restore_command = "cd " + project_path + ";"
    if os.path.exists(project_path + "/.git"):
        restore_command += "git reset --hard HEAD"
    elif os.path.exists(project_path + "/.svn"):
        restore_command += "svn revert -R .; "
    # print(restore_command)
    execute_command(restore_command)


def restore_all():
    Output.normal("restoring projects")
    Output.normal("\t" + Common.Project_A.path)
    restore_project(Common.Project_A.path)
    Output.normal("\t" + Common.Project_B.path)
    restore_project(Common.Project_B.path)
    Output.normal("\t" + Common.Project_C.path)
    restore_project(Common.Project_C.path)
    Output.normal("\t" + Common.Project_D.path)
    restore_project(Common.Project_D.path)


def soft_restore_all():
    Output.normal("restoring(soft) projects")
    Output.normal("\t" + Common.Project_A.path)
    soft_restore_project(Common.Project_A.path)
    Output.normal("\t" + Common.Project_B.path)
    soft_restore_project(Common.Project_B.path)
    Output.normal("\t" + Common.Project_C.path)
    soft_restore_project(Common.Project_C.path)
    Output.normal("\t" + Common.Project_D.path)
    soft_restore_project(Common.Project_D.path)




def clean_project(project_path):
    clean_command = "cd " + project_path + "; make clean; make distclean"
    execute_command(clean_command)


def clean_all():
    restore_all()
    Output.normal("cleaning projects")
    Output.normal("\t" + Common.Project_A.path)
    clean_project(Common.Project_A.path)

    Output.normal("\t" + Common.Project_B.path)
    clean_project(Common.Project_B.path)

    Output.normal("\t" + Common.Project_C.path)
    clean_project(Common.Project_C.path)

    Output.normal("\t" + Common.Project_D.path)
    clean_project(Common.Project_D.path)
