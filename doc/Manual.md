# Manual #
PatchWeave is a semantic based patch transplantation tool for C/C++ programs. It automatically finds the insertion location for the target program and adapt the patch to the namespace of the target program with the use of symbolic analysis. 
PatchWeave requires the source-code of the donor program and the target program, and the input that exercise the two programs to observe the common error. 

 ## Usage ##

In order to transplant a patch, PatchWeave requires a special build environment that supports LLVM-7 and LLVM-3.6 (Docker Image with all environment can be located at https://hub.docker.com/repository/docker/rshariffdeen/patchweave).
PatchWeave attempts to automatically detect the build setup using default build commands, it also provide the interface for customized build commands and configuration commands. 

PatchWeave requires a configuration file as input which provides values as following:

- path_a: absolute path for the directory of the source code of the donor program before the commit
- path_b: absolute path for the directory of the source code of the donor program after the commit
- path_c: absolute path for the directory of the source code of the target program
- exploit_command_a: command to use for the exploit(use $POC to indicate the position of a file input), from the root directory of the donor source code
- exploit_command_c: command to use for the exploit(use $POC to indicate the position of a file input), from the root directory of the target source code
- path_poc: absolute path for the file used for the exploit

Apart from the above configuration following additional configuration can be supplied to customize the workflow

- asan_flag: if build process requires any sanitizer, can be specified using this configuration
- build_command_a/_c: custom build command to use instead of built in PatchWeave make commands
- config_command_a/_c: custom config command to use instead of using built in PatchWeave configuration commands
- klee_flags_a/_c: custom flags to pass for the klee instrumented run (i.e. use of pre-built libraries to be linked)


### Side effects ###

**Warning!** PatchWeave executes arbitrary modifications of your source code which may lead to undesirable side effects. Therefore, it is recommended to run PatchWeave in an isolated environment.
Apart from that, PatchWeave produces the following side effects:

- prints log messages on the standard error output
- saves generated patch(es) in the current directory (i.e. output)
- saves intermediate data in the current directory (i.e. tmp)
- saves various log information in the current directory (i.e. logs)
- transforms/builds/tests the provided project

Typically, it is safe to execute PatchWeave consequently on the same copy of the project (without `make clean`), however idempotence cannot be guaranteed.
After PatchWeave terminates successfully, it restores the original source files, but does not restore files generated/modified by the tests and the build system.
If PatchWeave does not terminate successfully (e.g. by receiving `SIGKILL`), the source tree is likely to be corrupted.