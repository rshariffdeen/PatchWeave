# PatchWeave

Symbolic analysis based patch transplantation tool for C programs. PatchWeave transplants patches across programs which are semantically equivalent but syntactically different, to fix bugs/vulnerabilities that exist across multiple programs (i.e. recurring vulnerabilities)


## Docker Image ##

PatchWeave is distributed in source code form and pre-installed in Docker image. The Docker image also contains PatchWeave evaluation results.


You can [download](https://cloud.docker.com/repository/docker/rshariffdeen/patchweave) Docker image with pre-installed PatchWeave. Note that it contains multiple versions with and without the experiment results, use the correct tag for desired version.


## Documentation ##

* [Tutorial](doc/Tutorial.md)
* [Manual](doc/Manual.md)
* [Troubleshooting](doc/Troubleshooting.md)

To set optimal configuration for your subject, refer to the Configuration section of the [manual](doc/Manual.md).


## Contributors ##

Principal investigator:

* Abhik Roychoudhury

Developers:

* Ridwan Shariffdeen

Contributors:

* Shin Hwei Tan
* Ming Yuan
