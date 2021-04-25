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
exploit_command_c:/src/appl/imginfo -f $POC
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

* [Manual](doc/Manual.md)
* [Troubleshooting](doc/Troubleshooting.md)
* [Experiment Replication](doc/Replication.md)

To set optimal configuration for your subject, refer to the Configuration section of the [manual](doc/Manual.md).



## Citing PatchWeave

We are researchers, therefore if you use PatchWeave in an academic work we would be really glad if you cite our 
paper using the following bibtex:

```
@article{10.1145/3412376,
author = {Shariffdeen, Ridwan Salihin and Tan, Shin Hwei and Gao, Mingyuan and Roychoudhury, Abhik},
title = {Automated Patch Transplantation},
year = {2021},
issue_date = {January 2021},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
volume = {30},
number = {1},
issn = {1049-331X},
url = {https://doi.org/10.1145/3412376},
doi = {10.1145/3412376},
abstract = {Automated program repair is an emerging area that attempts to patch software errors and vulnerabilities. In this article, we formulate and study a problem related to automated repair, namely automated patch transplantation. A patch for an error in a donor program is automatically adapted and inserted into a “similar” target program. We observe that despite standard procedures for vulnerability disclosures and publishing of patches, many un-patched occurrences remain in the wild. One of the main reasons is the fact that various implementations of the same functionality may exist and, hence, published patches need to be modified and adapted. In this article, we therefore propose and implement a workflow for transplanting patches. Our approach centers on identifying patch insertion points, as well as namespaces translation across programs via symbolic execution. Experimental results to eliminate five classes of errors highlight our ability to fix recurring vulnerabilities across various programs through transplantation. We report that in 20 of 24 fixing tasks involving eight application subjects mostly involving file processing programs, we successfully transplanted the patch and validated the transplantation through differential testing. Since the publication of patches make an un-patched implementation more vulnerable, our proposed techniques should serve a long-standing need in practice.},
journal = {ACM Trans. Softw. Eng. Methodol.},
month = dec,
articleno = {6},
numpages = {36},
keywords = {code transplantation, dynamic program analysis, Program repair, patch transplantation}
}
```
## Developers / Maintainers
* Ridwan Shariffdeen


# License
This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details
