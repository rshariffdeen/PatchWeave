# Experiment Replication

PatchWeave successfully transplant patches for 20 defects in our benchmark. For each defect, we provide an
url that contains the developer patch and we provide the transplanted patch. We also include scripts to reproduce the experiment setup which can 
be evaluated using our tool. 

The following github repository includes scripts and Dockerfiles to re-create the experiment setup
Github Repo: https://github.com/rshariffdeen/patchweave-experiment

Pre-built Docker can be downloaded from following repository
Dockerhub Repo: https://hub.docker.com/repository/docker/rshariffdeen/patchweave

# Example Run
Following details how to run the scripts and the tool to replicate the results of our experiments.
Once you build the docker image, you spin up a container using following command

``
docker run -d -ti --name patchweave rshariffdeen/patchweave:experiments
``

Inside the container the following directories will be used
- /patchweave - this will be the tool directory
- /data - all experiment setups will be deployed in this directory

In /patchweave/experiment/patchweave directory a python script is provided to run all experiments. 
You can run all the experiments using the following command

``
python3 driver.py
``

You can specify the driver to setup the environment and manually run the tool later by using following command, which will 
setup the experiment data in /data directory. 

``
python3 driver.py --only-setup
``

You can also select a single test-case you want to replicate by running the following command, where the bug ID is the id specified in our benchmark.

``
python3 driver.py --bug-id=BUG_ID
``