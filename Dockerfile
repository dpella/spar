FROM ubuntu:focal

ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Europe/Stockholm

# Install system dependencies
RUN \
    apt-get update -y && \
    apt-get install -y --no-install-recommends \
        curl \
        libnuma-dev \
        zlib1g-dev \
        libgmp-dev \
        libgmp10 \
        git \
        wget \
        lsb-release \
        software-properties-common \
        gnupg2 \
        apt-transport-https \
        gcc \
        autoconf \
        automake \
        build-essential \
        libncurses5 \
        libncurses5-dev \
        z3

# Install ghcup
RUN \
    curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup > /usr/bin/ghcup && \
    chmod +x /usr/bin/ghcup

# Define GHC and cabal versions
ARG GHC=8.6.5
ARG CABAL=3.10.1.0

# Install GHC and cabal
RUN \
    ghcup -v install ghc --isolate /usr/local --force ${GHC} && \
    ghcup -v install cabal --isolate /usr/local/bin --force ${CABAL}

# Print installed versions
RUN ghc --version && cabal --version

# Update cabal package list
RUN cabal update

# Create a directory for Spar's source code and set it as the working directory
RUN mkdir -p /spar
WORKDIR /spar

# Add just the .cabal and cabal.project files to capture dependencies
COPY ./spar.cabal /spar/spar.cabal
COPY ./cabal.project /spar/cabal.project

# Docker will cache this command as a layer, freeing us up to modify source code
# without re-installing dependencies (unless the .cabal file changes!)
RUN cabal build --only-dependencies -j4

# Add and install Spar's library source code
COPY . /spar
RUN cabal build

# Set the entrypoint to the bash shell
CMD ["bash"]
