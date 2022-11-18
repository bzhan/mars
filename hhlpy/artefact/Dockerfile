FROM wolframresearch/wolframengine:13.0.1
FROM node:16.14.0

USER root
ARG DEBIAN_FRONTEND=noninteractive
WORKDIR /root

# Copy Wolfram Engine licence key (Wolfram engine is already installed in base image)
COPY mathpass /root/.WolframEngine/Licensing/mathpass

# Install python 3.9
RUN apt-get update -y
RUN apt-get install -y software-properties-common
RUN add-apt-repository -y ppa:deadsnakes/ppa
RUN apt-get update -y && apt-get upgrade -y
RUN apt install -y python3.9 python3.9-dev python3.9-venv
RUN python3.9 -m ensurepip

# Install required python packages
RUN python3.9 -m pip install lark
RUN python3.9 -m pip install sympy
RUN python3.9 -m pip install scipy
RUN python3.9 -m pip install wolframclient
RUN python3.9 -m pip install z3-solver==4.8.14.0

# Install git
RUN apt install -y git

# Install node modules
RUN npm install

# Clone the HHLPy project repo
RUN git clone https://gitee.com/bhzhan/mars.git

WORKDIR /root/mars

RUN git pull
RUN git checkout 4337980

# Set wolfram engine path so that HHLPy can find it
COPY wolframpath.txt ./hhlpy/wolframpath.txt

# Copy script to evaluate the benchmarks
COPY arch.py ./arch.py