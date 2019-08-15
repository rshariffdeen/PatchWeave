import subprocess

crash_word_list = ["abort", "core dumped", "crashed", "exception"]
error_word_list = ["runtime error", "buffer-overflow", "unsigned integer overflow"]
PATH_POC = ""
DIR_FUZZ_INPUT = ""
DIR_FUZZ_OUTPUT_LOG = ""
EXPLOIT_COMMAND = ""
PATH_A = ""
PATH_B = ""


def any_runtime_error(program_output):
    if any(error_word in str(program_output).lower() for error_word in error_word_list):
        return True
    return False


def compare_test_output(output_c, output_d):
    return_code_c, program_crashed_c, program_output_c = output_c
    return_code_d, program_crashed_d, program_output_d = output_d
    # print(output_c)
    # print(output_d)
    if str(program_output_c) == str(program_output_d):
        return 0
    else:
        if program_crashed_c:
            if program_crashed_d:
                if return_code_c == return_code_d:
                    if any_runtime_error(program_output_c):
                        if any_runtime_error(program_output_d):
                            return 0
                        else:
                            return 1
                    else:
                        if any_runtime_error(program_output_d):
                            return -1
                        else:
                            return 0
                else:
                    print(program_output_c)
                    print(program_output_d)
                    return -1
            else:
                return 1

        else:
            if program_crashed_d:
                print(program_output_c)
                print(program_output_d)
                exit(1)
            else:
                if return_code_c == return_code_d:
                    if any_runtime_error(program_output_c):
                        if any_runtime_error(program_output_d):
                            program_output_c = "\n".join(program_output_c)
                            program_output_d = "\n".join(program_output_d)
                            runtime_error_count_c = program_output_c.count("runtime error")
                            runtime_error_count_d = program_output_d.count("runtime error")
                            # print(runtime_error_count_c, runtime_error_count_d)
                            if runtime_error_count_d < runtime_error_count_c:
                                return 1
                            else:
                                return 0
                        else:
                            return 1
                    else:
                        if any_runtime_error(program_output_d):
                            return -1
                        else:
                            return 0
                else:
                    print(program_output_c)
                    print(program_output_d)
                    return -1


def run_exploit(exploit_command, project_path, poc_path, output_file_path, hide_output=False):
    exploit_command = str(exploit_command).replace('$POC', poc_path)
    exploit_command = "timeout 2m " + project_path + exploit_command + " > " + output_file_path + " 2>&1"
    # print(exploit_command)
    # Print executed command and execute it in console
    program_crashed = False
    process = subprocess.Popen([exploit_command], shell=True)
    output, error = process.communicate()
    program_output = ""
    return_code = ""
    with open(output_file_path, "r+") as output_file:
        program_output = output_file.readlines()
        if not hide_output:
            print(program_output)
        return_code = process.returncode
        program_output.append("RETURN CODE: " + str(return_code))
        output_file.writelines(program_output)

    if any(crash_word in str(program_output).lower() for crash_word in crash_word_list):
        program_crashed = True
        if not hide_output:
            print("\t\tprogram crashed with exit code " + str(return_code) + "\n")
    else:
        if return_code != 0:
            if not hide_output:
                print("\t\tprogram exited with exit code " + str(return_code) + "\n")
        else:
            if not hide_output:
                print("\t\tProgram did not crash!!" + "\n")

    return return_code, program_crashed, program_output[:-1]


def differential_test(file_extension, input_directory, exploit_command,
                      project_c_path, project_d_path, output_directory):
    print("analyzing fuzz inputs")
    count = 100
    fixes = 0
    errors = 0
    for i in range(0, 100):
        file_path = input_directory + "/" + str(i) + "." + file_extension
        log_file_name_c = output_directory + "/" + str(i) + "-c"
        pc_output = run_exploit(exploit_command,
                                          project_c_path,
                                          file_path,
                                          log_file_name_c,
                                          True)

        log_file_name_d = output_directory + "/" + str(i) + "-d"
        pd_output = run_exploit(exploit_command,
                                          project_d_path,
                                          file_path,
                                          log_file_name_d,
                                          True)

        result = compare_test_output(pc_output, pd_output)

        if result == 1:
            fixes += 1
        elif result == -1:
            errors += 1

    print("\t\tTotal test: " + str(count))
    print("\t\tTotal test that passed only in Pd: " + str(fixes))
    print("\t\tTotal test that failed only in Pd: " + str(errors))


def execute_command(command, show_output=True):
    # Print executed command and execute it in console
    command = "{ " + command + " ;} 2> " + "error_log"
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return str(process.returncode)


def generate_files(poc_path, output_directory):
    count = 100
    file_extension = poc_path.split(".")[-1]
    print("generating fuzzed inputs")
    for i in range(0, 100):
        generate_command = "radamsa " + str(poc_path) + " > " + output_directory + "/" + str(i) + "." + file_extension
        execute_command(generate_command)
    print("\t\t[completed] generating 100 fuzzed input files")
    return file_extension


def verify_behavior():
    file_extension = generate_files(PATH_POC, DIR_FUZZ_INPUT)
    differential_test(file_extension, DIR_FUZZ_INPUT, EXPLOIT_COMMAND, PATH_A, PATH_B, DIR_FUZZ_OUTPUT_LOG)


verify_behavior()
