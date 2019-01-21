#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_model
import Output
import Common
import Logger
import Concolic
import Generator
import Tracer
import Weaver


KLEE_SYMBOLIC_ENGINE = "klee "
SYMBOLIC_ARGUMENTS = "--no-exit-on-error --libc=uclibc --posix-runtime --external-calls=all --only-replay-seeds --seed-out=$KTEST"
TOOL_KLEE_INSTRUMENTATION = "/home/ridwan/workspace/llvm/llvm-7/build/bin/gizmo"
FILE_TEMP_INSTRUMENTED = Common.DIRECTORY_OUTPUT + "/temp-instrumented"

var_expr_map_a = dict()
var_expr_map_b = dict()
var_expr_map_c = dict()


def collect_symbolic_expressions(trace_file_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tcollecting symbolic expressions")
    var_expr_map = dict()
    if os.path.exists(trace_file_path):
        with open(trace_file_path, 'r') as trace_file:
            for line in trace_file:
                if '[var-expr]' in line:
                    line = line.replace("[var-expr] ", "")
                    var_name, var_expr = line.split(":")
                    var_expr_map[var_name] = var_expr
    return var_expr_map


def build_instrumented_code(source_directory):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\t\tbuilding instrumented code")
    CXX_FLAGS = "'-g -O0 -static -DNDEBUG -ftrapv'"
    C_FLAGS = "'-g -O0 -static -ftrapv -L/home/rshariffdeen/workspace/klee/build-rshariffdeen/lib -lkleeRuntest'"
    build_command = "cd " + source_directory + ";"
    build_command += "make CFLAGS=" + C_FLAGS + " "
    build_command += "CXXFLAGS=" + CXX_FLAGS + " > " + Common.FILE_MAKE_LOG
    # print(build_command)
    ret_code = execute_command(build_command)
    if int(ret_code) != 0:
        Output.error(build_command)
        error_exit("BUILD FAILED!!\nExit Code: " + str(ret_code))


def read_variable_name(source_path, start_pos, end_pos):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    start_line, start_column = start_pos
    end_line, end_column = end_pos
    if start_line != end_line:
        print("LINE NOT SAME")
        exit()
    source_line = ""
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            source_line = str(content[start_line-1]).strip()

    var_name = source_line[start_column-3:end_column-2]
    return var_name.strip()


def instrument_code_for_klee(source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\t\tinstrumenting source code")
    variable_list = generate_available_variable_list(source_path, line_number)
    insert_code = "\n"
    for variable in variable_list:
        insert_code += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            content[int(line_number)-1] = insert_code
    with open(source_path, 'w') as source_file:
        source_file.writelines(content)


def collect_var_dec_list(ast_node, line_number, source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    child_count = len(ast_node['children'])
    start_line = int(ast_node['start line'])
    end_line = int(ast_node['end line'])
    start_column = int(ast_node['start column'])
    end_column = int(ast_node['end column'])
    node_type = ast_node['type']

    if start_line == int(line_number):
        return var_list

    if node_type in ["ParmVarDecl", "VarDecl"]:
        var_name = str(ast_node['identifier'])
        var_list.append(var_name)
        return var_list

    if child_count:
        for child_node in ast_node['children']:
            var_list = var_list + list(set(collect_var_dec_list(child_node, line_number, source_path)))
    return list(set(var_list))


def collect_var_ref_list(ast_node, line_number, source_path):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    child_count = len(ast_node['children'])
    start_line = int(ast_node['start line'])
    end_line = int(ast_node['end line'])
    start_column = int(ast_node['start column'])
    end_column = int(ast_node['end column'])
    node_type = ast_node['type']

    if start_line == int(line_number):
        return var_list

    if node_type in ["MemberExpr"]:
        node_value = ast_node['value']
        var_name = ""
        if node_value == "":
            return var_list
        var_name = str(node_value.split(":")[-1])
        child_node = ast_node['children'][0]
        while child_node:
            child_node_type = child_node['type']
            if child_node_type == "DeclRefExpr":
                var_name = str(child_node['value']) + "->" + var_name
            elif child_node_type == "ArraySubscriptExpr":
                return var_list
            elif child_node_type == "MemberExpr":
                var_name = str(child_node['value'].split(":")[-1]) + "->" + var_name
            else:
                print(ast_node)
                exit()
            if len(child_node['children']) > 0:
                child_node = child_node['children'][0]
            else:
                child_node = None
        var_list.append(var_name)
        return var_list
    if child_count:
        for child_node in ast_node['children']:
            var_list = var_list + list(set(collect_var_ref_list(child_node, line_number, source_path)))
    return list(set(var_list))


def generate_available_variable_list(source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\t\t\tgenerating variable(available) list")
    variable_list = list()
    ast_map = Generator.get_ast_json(source_path)
    func_node = Weaver.get_fun_node(ast_map, int(line_number), source_path)
    param_node = func_node['children'][0]
    for child_node in param_node['children']:
        child_node_type = child_node['type']
        if child_node_type == "ParmVarDecl":
            var_name = str(child_node['identifier'])
            if var_name not in variable_list:
                variable_list.append(var_name)

    compound_node = func_node['children'][1]
    for child_node in compound_node['children']:
        child_node_type = child_node['type']
        child_node_start_line = child_node['start line']
        child_node_end_line = child_node['end line']
        filter_declarations = False
        child_var_dec_list = collect_var_dec_list(child_node, line_number, source_path)
        child_var_ref_list = collect_var_ref_list(child_node, line_number, source_path)

        if child_node_start_line <= line_number <= child_node_end_line:
            variable_list = list(set(variable_list + child_var_ref_list + child_var_dec_list))
            break

        if child_node_type in ["IfStmt", "ForStmt"]:
            filter_var_ref_list = list()
            for var_ref in child_var_ref_list:
                if var_ref in child_var_dec_list:
                    child_var_ref_list.remove(var_ref)
                elif "->" in var_ref:
                    var_name = var_ref.split("->")[0]
                    if var_name in child_var_dec_list:
                        filter_var_ref_list.append(var_ref)
            child_var_ref_list = list(set(child_var_ref_list) - set(filter_var_ref_list))
            variable_list = list(set(variable_list + child_var_ref_list))
        else:
            variable_list = list(set(variable_list + child_var_ref_list + child_var_dec_list))
    return variable_list


def generate_symbolic_expressions(source_path, line_number):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    binary_path = Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0]
    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    backup_command = "cp " + binary_path + "/" + binary_name + ".bc " + binary_path + "/" + binary_name + ".bc.bk"
    execute_command(backup_command)

    instrument_code_for_klee(source_path, line_number)
    build_instrumented_code(source_directory)
    Concolic.extract_bitcode(Common.VALUE_PATH_C + Common.VALUE_EXPLOIT_C.split(" ")[0])
    Concolic.concolic_execution(" ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:]), binary_path, binary_name, Weaver.FILE_VAR_EXPR_LOG, True)
    var_expr_map_c = collect_symbolic_expressions(Weaver.FILE_VAR_EXPR_LOG)
    print(var_expr_map_c)
    restore_command = "cp " + binary_path + "/" + binary_name + ".bc.bk " + binary_path + "/" + binary_name + ".bc"
    execute_command(restore_command)
    reset_command = "cd " + source_directory + ";git reset --hard HEAD"
    execute_command(reset_command)
    exit()
    #
    # generate_command = "cd " + binary_path + ";"
    # generate_command += SYMBOLIC_ENGINE + SYMBOLIC_ARGUMENTS.replace("$KTEST",
    #                                                               FILE_SYMBOLIC_POC) + " " + binary_name + ".bc " \
    #                  + binary_arguments.replace("$POC", "A") + " --sym-files 1 " + str(
    #     VALUE_BIT_SIZE) + "  > " + log_path + \
    #                  " 2>&1"
    # # print(trace_command)
    # execute_command(trace_command)


def get_model_from_solver(str_formula):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    parser = SmtLibParser()
    script = parser.get_script(cStringIO(str_formula))
    formula = script.get_last_formula()
    model = get_model(formula, solver_name="z3")
    if not hasattr(model, '__dict__'):
        return None
    return model.__dict__['z3_model']


def extract_values_from_model(model):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    byte_array = dict()
    for dec in model.decls():
        if dec.name() == "A-data":
            var_list = model[dec].as_list()
            for pair in var_list:
                if type(pair) == list:
                    byte_array[pair[0]] = pair[1]
    return byte_array


def generate_z3_code_for_expr(var_expr):
    code = "(set-logic QF_AUFBV )\n"
    code += "(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
    code += "(declare-fun a () (_ BitVec 32))\n"
    code += "(declare-fun b () (_ BitVec 32))\n"
    code += "(assert (= a " + var_expr + "))\n"
    code += "(assert (not (= b #x00000000)))\n"
    code += "(assert  (= a b) )\n"
    code += "(check-sat)"
    return code


def get_input_bytes_used(sym_expr):
    model_a = get_model_from_solver(sym_expr)
    input_byte_list = list()
    if model_a is not None:
        input_bytes_map = extract_values_from_model(model_a)
        input_byte_list = list(set(input_bytes_map.keys()))
    return input_byte_list


def generate_mapping(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating variable map")
    for var_a in var_map_a:
        sym_expr = generate_z3_code_for_expr(var_map_a[var_a])
        input_bytes_a = get_input_bytes_used(sym_expr)
        candidate_list = list()
        for var_b in var_map_b:
            sym_expr = generate_z3_code_for_expr(var_map_b[var_b])
            input_bytes_b = get_input_bytes_used(sym_expr)
            if input_bytes_a == input_bytes_b:
                candidate_list.append(var_b)

