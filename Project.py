# -*- coding: utf-8 -*-

import os
from Utilities import error_exit, execute_command
import Output
import Common


class Project:
    def __init__(self, path, name, exploit=''):
        if not (os.path.isdir(path)):
            Output.error(name + " is not an appropriate directory path.")
            exit()
        if path[-1] != "/":
            path += "/"
        self.path = path
        self.name = name
        self.exploit = exploit
        self.functions = dict()
        self.structs = dict()
        self.clean()
        try:
            if not (os.path.isfile(path + "/compile_commands.json")):
                self.make(bear=True)
            else:
                cat_command = "cat " + path + "/compile_commands.json"
                if int(len(execute_command(cat_command)[0])) <= 2:
                    self.make(bear=True)      
                
        except Exception as exception:
            error_exit(exception, "Failed at bear making project. Check configuration.")

    def make(self, bear=False):
        command = "cd " + self.path + "; make clean;"
        if bear:
            command += "bear "
        command += "make > " + Common.DIRECTORY_OUTPUT + "/compile_warnings;"
        execute_command(command)
        command = "cd " + Common.DIRECTORY_MAIN
        execute_command(command)
        
    def clean(self):
        # Remove *.crochetAST, *.AST and *.vec files from directory
        Output.normal("Cleaning " + self.name + "...")
        #clean_ASTs(self.path)