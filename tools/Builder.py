#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import os
import sys
from common.Utilities import execute_command, error_exit
from common import Definitions, Values
from tools import Logger, Emitter

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
        Emitter.error(config_command)
        error_exit("CONFIGURATION FAILED!!\nExit Code: " + str(ret_code))


def build_project(project_path, build_command=None):
    dir_command = "cd " + project_path + ";"
    if build_command is None:
        build_command = "bear make CFLAGS=" + C_FLAGS + " "
        build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + Definitions.FILE_MAKE_LOG
    build_command = dir_command + build_command
    # print(build_command)
    ret_code = execute_command(build_command)
    if int(ret_code) != 0:
        Emitter.error(build_command)
        error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))


def build_all():
    Emitter.normal("building")

    Emitter.normal("\t" + Values.Project_A.path)
    if not Values.BUILD_COMMAND_A:
        build_project(Values.Project_A.path)
    else:
        build_project(Values.Project_A.path, Values.BUILD_COMMAND_A)

    Emitter.normal("\t" + Values.Project_B.path)
    if not Values.BUILD_COMMAND_A:
        build_project(Values.Project_B.path)
    else:
        build_project(Values.Project_B.path, Values.BUILD_COMMAND_A)

    Emitter.normal("\t" + Values.Project_C.path)
    if not Values.BUILD_COMMAND_C:
        build_project(Values.Project_C.path)
    else:
        build_project(Values.Project_C.path, Values.BUILD_COMMAND_C)

    Emitter.normal("\t" + Values.Project_D.path)
    if not Values.BUILD_COMMAND_C:
        build_project(Values.Project_D.path)
    else:
        build_project(Values.Project_D.path, Values.BUILD_COMMAND_C)


def config_all(is_llvm=False):
    Emitter.normal("configuring projects")

    Emitter.normal("\t" + Values.Project_A.path)
    if not Values.BUILD_COMMAND_A:
        config_project(Values.Project_A.path, is_llvm)

    Emitter.normal("\t" + Values.Project_B.path)
    if not Values.BUILD_COMMAND_A:
        config_project(Values.Project_B.path, is_llvm)

    Emitter.normal("\t" + Values.Project_C.path)
    if not Values.BUILD_COMMAND_C:
        config_project(Values.Project_C.path, is_llvm)

    Emitter.normal("\t" + Values.Project_D.path)
    if not Values.BUILD_COMMAND_C:
        config_project(Values.Project_D.path, is_llvm)


def build_normal():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Emitter.sub_title("building projects")
    CC = "clang"
    CXX = "clang++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    build_all()


def build_verify():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Emitter.sub_title("building projects")
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    Emitter.normal("\t" + Values.Project_D.path)
    if not Values.BUILD_COMMAND_C:
        build_project(Values.Project_D.path)
    else:
        build_project(Values.Project_D.path, Values.BUILD_COMMAND_C)


def build_asan():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Emitter.sub_title("building projects with asan")
    clean_all()
    CC = "clang"
    CXX = "clang++"
    CXX_FLAGS = "'-g -O0 -static'"
    C_FLAGS = "'-g -O0 -static'"
    config_all()
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + Values.ASAN_FLAG + "'"
    C_FLAGS = "'-g -O0 -static -DNDEBUG -fsanitize=" + Values.ASAN_FLAG + "'"
    build_all()


def build_llvm():
    global CC, CXX, CXX_FLAGS, C_FLAGS, LD_FLAGS
    Emitter.sub_title("building projects with wllvm")
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
    Emitter.normal("restoring projects")
    Emitter.normal("\t" + Values.Project_A.path)
    restore_project(Values.Project_A.path)
    Emitter.normal("\t" + Values.Project_B.path)
    restore_project(Values.Project_B.path)
    Emitter.normal("\t" + Values.Project_C.path)
    restore_project(Values.Project_C.path)
    Emitter.normal("\t" + Values.Project_D.path)
    restore_project(Values.Project_D.path)


def soft_restore_all():
    Emitter.normal("restoring(soft) projects")
    Emitter.normal("\t" + Values.Project_A.path)
    soft_restore_project(Values.Project_A.path)
    Emitter.normal("\t" + Values.Project_B.path)
    soft_restore_project(Values.Project_B.path)
    Emitter.normal("\t" + Values.Project_C.path)
    soft_restore_project(Values.Project_C.path)
    Emitter.normal("\t" + Values.Project_D.path)
    soft_restore_project(Values.Project_D.path)


def clean_project(project_path):
    clean_command = "cd " + project_path + "; make clean; make distclean"
    execute_command(clean_command)


def clean_all():
    restore_all()
    Emitter.normal("cleaning projects")
    Emitter.normal("\t" + Values.Project_A.path)
    clean_project(Values.Project_A.path)

    Emitter.normal("\t" + Values.Project_B.path)
    clean_project(Values.Project_B.path)

    Emitter.normal("\t" + Values.Project_C.path)
    clean_project(Values.Project_C.path)

    Emitter.normal("\t" + Values.Project_D.path)
    clean_project(Values.Project_D.path)


def build_instrumented_code(source_directory):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Emitter.normal("\t\tbuilding instrumented code")
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -ftrapv -L/home/rshariffdeen/workspace/klee/build-rshariffdeen/lib -lkleeRuntest'"
    build_command = "cd " + source_directory + ";"
    build_command += "make CFLAGS=" + C_FLAGS + " "
    build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + Definitions.FILE_MAKE_LOG
    # print(build_command)
    ret_code = execute_command(build_command)
    if int(ret_code) == 2:
        # TODO: check only upto common directory
        while source_directory != "" and ret_code != "0":
            build_command = build_command.replace(source_directory, "???")
            source_directory = "/".join(source_directory.split("/")[:-1])
            build_command = build_command.replace("???", source_directory)
            ret_code = execute_command(build_command)

    if int(ret_code) != 0:
        Emitter.error(build_command)
        error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))
