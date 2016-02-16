# change these values for each container
# note: test1 is actually copied from algorun/input_example.txt, algorun/output_example.txt
# the others should be named e.g. test2-input.json, test2-output.json
TESTS = test1 test2 test3 test4

# the port number  should be different for each type of container
PORT = 31335
CONTAINER_NAME = react

# see the following file for the available
# make targets, or do 'make help'
include ../share/include-Makefile
