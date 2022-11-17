#!/bin/sh

VERSION=$(grep -o 'clone -b z3-[^ ]*' Dockerfile | sed -e 's/.* z3-//')
echo "Building z3 $VERSION"

docker build -t z3-centos7 .
docker run -v $(pwd):/dist:z z3-centos7 scl enable devtoolset-7 'python3 scripts/mk_make.py --prefix=/dist; cd build; make && make install'

mkdir -p starexec
mkdir -p starexec/bin
mkdir -p starexec/src
echo "z3 $VERSION" > starexec/starexec_description.txt
cp bin/z3 starexec_run_default starexec/bin
cp README Dockerfile starexec_run_default starexec_run_fixmodel z3-fix-model.pl build-z3-starexec.sh starexec/src
cd starexec
zip -r ../z3-$VERSION-starexec.zip .
cd ..

mkdir -p starexecmv
mkdir -p starexecmv/bin
mkdir -p starexecmv/src
echo "z3 $VERSION mv" > starexecmv/starexec_description.txt
cp bin/z3 z3-fix-model.pl starexecmv/bin/
cp starexec_run_fixmodel starexecmv/bin/starexec_run_default
cp README Dockerfile starexec_run_default starexec_run_fixmodel z3-fix-model.pl build-z3-starexec.sh starexecmv/src
cd starexecmv
zip -r ../z3-$VERSION-mv-starexec.zip .
cd ..
