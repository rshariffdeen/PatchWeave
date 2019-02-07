#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import sys, os
sys.path.append('./ast/')
import time
from Utilities import execute_command, error_exit, backup_file, restore_file, extract_bitcode, reset_git, is_intersect
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
                    var_expr_map[var_name] = var_expr.replace("\n", "")
    return var_expr_map


def build_instrumented_code(source_directory):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tbuilding instrumented code")
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


def instrument_code_for_klee(source_path, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tinstrumenting source code")
    variable_list = generate_available_variable_list(source_path, start_line, end_line, only_in_range)
    insert_code = "\n"
    for variable in variable_list:
        insert_code += "klee_print_expr(\"[var-expr] " + variable + "\", " + variable + ");\n"
    insert_code += "exit(-1);"
    # print(insert_code)
    insert_line = 0
    if Common.Project_B.path in source_path:
        insert_line = int(start_line) - 1
    else:
        insert_line = int(end_line) - 1
    if os.path.exists(source_path):
        with open(source_path, 'r') as source_file:
            content = source_file.readlines()
            existing_line = content[insert_line]
            content[insert_line] = existing_line + insert_code
    with open(source_path, 'w') as source_file:
        source_file.writelines(content)


def collect_var_dec_list(ast_node, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    child_count = len(ast_node['children'])
    node_start_line = int(ast_node['start line'])
    node_end_line = int(ast_node['end line'])
    start_column = int(ast_node['start column'])
    end_column = int(ast_node['end column'])
    node_type = ast_node['type']

    if only_in_range:
        if not is_intersect(node_start_line, node_end_line, start_line, end_line):
            return var_list

    if node_type in ["ParmVarDecl", "VarDecl"]:
        var_name = str(ast_node['identifier'])
        var_list.append(var_name)
        return var_list

    if child_count:
        for child_node in ast_node['children']:
            var_list = var_list + list(set(collect_var_dec_list(child_node, start_line, end_line, only_in_range)))
    return list(set(var_list))


def collect_var_ref_list(ast_node, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_list = list()
    child_count = len(ast_node['children'])
    node_start_line = int(ast_node['start line'])
    node_end_line = int(ast_node['end line'])
    start_column = int(ast_node['start column'])
    end_column = int(ast_node['end column'])
    node_type = ast_node['type']

    if only_in_range:
        if not is_intersect(node_start_line, node_end_line, start_line, end_line):
            return var_list

    if node_type in ["MemberExpr"]:
        node_value = ast_node['value']

        var_name = ""
        if node_value == "":
            return var_list
        var_name = str(node_value.split(":")[-1])
        if "union" in node_value:
            var_name = "." + var_name
        else:
            var_name = "->" + var_name
        child_node = ast_node['children'][0]
        while child_node:
            child_node_type = child_node['type']
            if child_node_type == "DeclRefExpr":
                var_name = str(child_node['value']) + var_name
            elif child_node_type == "ArraySubscriptExpr":
                iterating_var_node = child_node['children'][1]
                iterating_var_name = iterating_var_node['value']
                iterating_var_type = iterating_var_node['type']
                if iterating_var_type == "DeclRefExpr":
                    iterating_var_ref_type = iterating_var_node['ref_type']
                    if iterating_var_ref_type in ["VarDecl", "ParmVarDecl"]:
                        var_list.append(iterating_var_name)
                        if var_name[:2] == "->":
                            var_name = "." + var_name[2:]
                        var_name = "[" + iterating_var_name + "]" + var_name
            elif child_node_type == "MemberExpr":
                child_node_value = child_node['value']
                if "union" in child_node_value:
                    var_name = "." + str(child_node_value.split(":")[-1]) + var_name
                else:
                    var_name = "->" + str(child_node_value.split(":")[-1]) + var_name
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
            var_list = var_list + list(set(collect_var_ref_list(child_node, start_line, end_line, only_in_range)))
    return list(set(var_list))


def generate_available_variable_list(source_path, start_line, end_line, only_in_range):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\t\tgenerating variable(available) list")
    variable_list = list()
    ast_map = Generator.get_ast_json(source_path)
    func_node = Weaver.get_fun_node(ast_map, int(end_line), source_path)
    # print(source_path, start_line, end_line)
    if not only_in_range:
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
        child_node_start_line = int(child_node['start line'])
        child_node_end_line = int(child_node['end line'])
        filter_declarations = False
        # print(child_node_start_line, child_node_end_line)
        child_var_dec_list = collect_var_dec_list(child_node, start_line, end_line, only_in_range)
        child_var_ref_list = collect_var_ref_list(child_node, start_line, end_line, only_in_range)
        if child_node_start_line <= int(end_line) <= child_node_end_line:
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


def generate_symbolic_expressions(source_path, start_line, end_line, output_log, only_in_range=True):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\tgenerating symbolic expressions")
    source_file_name = str(source_path).split("/")[-1]
    source_directory = "/".join(str(source_path).split("/")[:-1])

    if Common.Project_A.path in source_path:
        binary_path = Common.Project_A.path + Common.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Common.Project_B.path in source_path:
        binary_path = Common.Project_B.path + Common.VALUE_EXPLOIT_A.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_A.split(" ")[1:])
    elif Common.Project_C.path in source_path:
        binary_path = Common.Project_C.path + Common.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:])
    else:
        binary_path = Common.Project_D.path + Common.VALUE_EXPLOIT_C.split(" ")[0]
        binary_args = " ".join(Common.VALUE_EXPLOIT_C.split(" ")[1:])

    binary_name = str(binary_path).split("/")[-1]
    binary_directory = "/".join(str(binary_path).split("/")[:-1])
    backup_file(binary_path, "original-bitcode")

    instrument_code_for_klee(source_path, start_line, end_line, only_in_range)
    build_instrumented_code(source_directory)
    extract_bitcode(binary_path)
    Concolic.generate_var_expressions(binary_args, binary_directory, binary_name, output_log)
    restore_file("original-bitcode", binary_path)
    reset_git(source_directory)


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
    # print(model)
    for dec in model.decls():
        # print(dec)
        # print(model[dec])
        if dec.name() == "A-data":
            if hasattr(model[dec], "num_entries"):
                var_list = model[dec].as_list()
                # print(var_list)
                for pair in var_list:
                    if type(pair) == list:
                        byte_array[pair[0]] = pair[1]
            else:
                return None

    return byte_array


def create_z3_code(var_expr, var_name, bit_size):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = var_name + "_" + str(bit_size)
    if bit_size == 64:
        zero = "x0000000000000000"
    else:
        zero = "x00000000"
    code = "(set-logic QF_AUFBV )\n"
    code += "(declare-fun A-data () (Array (_ BitVec 32) (_ BitVec 8) ) )\n"
    code += "(declare-fun " + var_name + "() (_ BitVec " + str(bit_size) + "))\n"
    # code += "(declare-fun b () (_ BitVec " + str(bit_size) + "))\n"
    code += "(assert (= " + var_name + " " + var_expr + "))\n"
    # code += "(assert (not (= b #" + zero + ")))\n"
    code += "(assert  (not (= " + var_name + " #" + zero + ")))\n"
    code += "(check-sat)"
    return code


def generate_z3_code_for_expr(var_expr, var_name):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    var_name = str(var_name).replace("->", "")
    var_name = str(var_name).replace("[", "-")
    var_name = str(var_name).replace("]", "-")
    count_64 = int(var_expr.count("64)"))
    count_bracket = int(var_expr.count(")"))

    if count_bracket == 1:
        if count_64 == 1:
            code = create_z3_code(var_expr, var_name, 64)
        else:
            code = create_z3_code(var_expr, var_name, 32)
    else:

        try:
            code = create_z3_code(var_expr, var_name, 32)
            parser = SmtLibParser()
            script = parser.get_script(cStringIO(code))
            formula = script.get_last_formula()
        except Exception as exception:
            code = create_z3_code(var_expr, var_name, 64)
    return code


def get_input_bytes_used(sym_expr):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    model_a = get_model_from_solver(sym_expr)
    # print(model_a)
    input_byte_list = list()
    if model_a is not None:
        input_bytes_map = extract_values_from_model(model_a)
        if input_bytes_map is None:
            script_lines = str(sym_expr).split("\n")
            value_line = script_lines[3]
            tokens = value_line.split("A-data")
            if len(tokens) > 2:
                error_exit("MORE than expected!!")
            else:
                byte_index = ((tokens[1].split(")")[0]).split("bv")[1]).split(" ")[0]
                input_byte_list.append(int(byte_index))
        else:
            input_byte_list = list(set(input_bytes_map.keys()))
    return input_byte_list


def generate_mapping(var_map_a, var_map_b):
    Logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    Output.normal("\t\tgenerating variable map")
    var_map = dict()

    for var_a in var_map_a:
        # print(var_a)
        sym_expr = generate_z3_code_for_expr(var_map_a[var_a], var_a)
        # print(sym_expr)
        input_bytes_a = get_input_bytes_used(sym_expr)
        # print(input_bytes_a)
        candidate_list = list()
        for var_b in var_map_b:
            # print(var_b)
            sym_expr = generate_z3_code_for_expr(var_map_b[var_b], var_b)
            # print(sym_expr)
            input_bytes_b = get_input_bytes_used(sym_expr)
            # print(input_bytes_b)
            if input_bytes_a and input_bytes_a == input_bytes_b:
                candidate_list.append(var_b)
        if len(candidate_list) == 1:
            var_map[var_a] = candidate_list[0]
        elif len(candidate_list) > 1:
            print(candidate_list)
            print("more than one candidate")
            exit()
    return var_map
