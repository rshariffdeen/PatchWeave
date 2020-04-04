# PatchWeave

Semantic based patch transplantation tool for C programs. PatchWeave transplants patches across programs which are semantically equivalent but syntactically different, to fix bugs/vulnerabilities that exist across multiple programs (i.e. recurring vulnerabilities)


## Docker Image ##

PatchWeave is distributed in source code form and pre-installed in Docker image. The Docker image also contains PatchWeave evaluation results.


You can [download](https://cloud.docker.com/repository/docker/rshariffdeen/patchweave) Docker image with pre-installed PatchWeave. Note that it contains multiple versions with and without the experiment results, use the correct tag for desired version.


## Example Usage ##
PatchWeave requires a configuration file which specifies the source code path to the donor program and
the target program. Following is an example configuration file for bug id 1, as provided in our docker image

```c
path_a:/data/openjpeg-jasper/div-zero-1/openjpeg-1.5.1;
path_b:/data/openjpeg-jasper/div-zero-1/openjpeg-1.5.2;
path_c:/data/openjpeg-jasper/div-zero-1/jasper-1.900.2
exploit_command_c:/src/appl/imginfo -f $POC\
exploit_command_a:/applications/codec/j2k_to_image -i $POC -o out.bmp
path_poc:/data/exploits/jasper/CVE-2016-8691.j2k
asan_flag:integer
```

Once you setup a configuration file as above you can use the following command to run PatchWeave which will transplant the patch
from OpenJPEG to Jasper.

``
python PatchWeave.py --conf=/path/to/conf/file
``

## Documentation ##

* [Tutorial](doc/Tutorial.md)
* [Manual](doc/Manual.md)
* [Troubleshooting](doc/Troubleshooting.md)
* [Experiment Replication](doc/Replication.md)

To set optimal configuration for your subject, refer to the Configuration section of the [manual](doc/Manual.md).


## Contributors ##

Principal investigator:

* Abhik Roychoudhury

Developers:

* Ridwan Shariffdeen

Contributors:

* Shin Hwei Tan
* Ming Yuan
