#! /usr/bin/env python3
# -*- coding: utf-8 -*-


from common import Definitions
from tools import Emitter, Builder
from phases import Trace


def build():
    Emitter.title("Building projects")
    if not Definitions.NO_BUILD:
        Builder.build_asan()
        Trace.test_exploits()
        Builder.build_llvm()
    else:
        Builder.soft_restore_all()
