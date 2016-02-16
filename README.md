# Reverse Engineering with Evolutionary Computation Tools (REACT)

REACT is an Evolutionary Algorithm for Discrete Dynamical Systems' Optimization

## AUTHORS ##

Paola Vera-Licona & John J. McGee Virginia Bioinformatics Institute at Virginia Tech

## ABOUT ##

The inference of gene regulatory networks (GRNs) from system-level experimental observations is at the heart of systems biology due to its centrality in gaining insight into the complex regulatory mechanisms in cellular systems. This includes the inference of both the network topology and dynamic mathematical models.

This software contains a novel network inference algorithm within the algebraic framework of Boolean polynomial dynamical system (BPDS). The algorithm considers time series data, including that of perturbation experiments such as knock-out mutants and RNAi experiments. To infer the network topology and dynamic models, it allows for the incorporation of prior biological knowledge while being robust to significant levels of noise in the data used for inference. It uses an evolutionary algorithm for local optimization with an encoding of the mathematical models as BPDS.

More info: http://www.paola-vera-licona.net/Software/EARevEng/REACT.html

## HOW TO RUN REACT ##

REACT has been made available as an AlgoRun Docker container to make it easy to run anywhere without tedious technical manipulation. For more information about Docker, see http://docker.com
The REACT docker image is available on Docker Hub as: algorun/react

1. Install docker
See https://docs.docker.com/

2. Run the REACT docker image
sudo docker run -d -p 31331:8765 --name react algorun/react
This will automatically pull the algorun/react docker image from docker hub.
Note that you can pick an other port number than 31331

3. Test that the REACT docker image is running correctly
You can try the algorithm by navigating to http://localhost:31331 in the web browser

5. [optional] to stop and delete the container
sudo docker kill react
sudo docker rm react

## HOW TO REBUILD THE DOCKER IMAGE ##

If you change the REACT code, you will need to rebuild the docker image:
sudo docker build -t <your username>/react .
