#!/bin/bash

# Build the docker image
docker build -t spar-library .

# Run the docker container
docker run --rm -it spar-library