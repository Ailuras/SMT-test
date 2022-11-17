FROM centos:7
RUN yum -y install gcc gcc-c++ make flex bison glibc-static libstdc++-static python3 cython git

RUN git clone -b z3-4.8.11 https://github.com/Z3Prover/z3

RUN yum -y install centos-release-scl
RUN yum -y install devtoolset-7
WORKDIR /z3

