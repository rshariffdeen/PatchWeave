# -*- coding: utf-8 -*-

import os
from tools import Emitter


class Project:
    def __init__(self, path, name, exploit=''):
        Emitter.information("creating project for " + path)
        if not (os.path.isdir(path)):
            Emitter.error(path + " is not an appropriate directory path.")
            exit()
        if path[-1] != "/":
            path += "/"
        self.path = path
        self.name = name
        self.exploit = exploit
        self.functions = dict()
        self.structs = dict()

        # try:
        #     if not (os.path.isfile(path + "/compile_commands.json")):
        #         self.make(bear=True)
        #     else:
        #         cat_command = "cat " + path + "/compile_commands.json"
        #         if int(len(execute_command(cat_command)[0])) <= 2:
        #             self.make(bear=True)
        #
        # except Exception as exception:
        #     error_exit(exception, "Failed at bear making project. Check configuration.")
