# testgen-js [![Build Status][travis-image]][travis-url]

[travis-url]: https://travis-ci.com/hakatashi/testgen.js
[travis-image]: https://travis-ci.com/hakatashi/testgen.js.svg?token=LBP6dMS3oXazpwBS3Fws&branch=master

> An experimental project to automatically generate test cases for given JavaScript code.

## Prerequisites

### Install SpiderMonkey

```
cd /tmp
git clone --depth 1 https://github.com/mozilla/gecko-dev.git
cd gecko-dev/js/src
autoconf2.13
mkdir build_DBG.OBJ
cd build_DBG.OBJ
../configure --enable-debug --disable-optimize
make
sudo make install
```

Make sure `js74` command will be available.

### Install CVC4

```
cd /tmp
git clone --depth 1 https://github.com/CVC4/CVC4.git
cd CVC4
./contrib/get-antlr-3.4
./contrib/get-symfpu
./contrib/get-cadical
./contrib/get-cryptominisat
./contrib/get-lfsc
./configure.sh --symfpu --cadical --cryptominisat --lfsc
mkdir build
cd build
make
make install
```

Make sure `cvc4` command will be available.

### Install Rust

Follow the instruction in https://rustup.rs/ and install nightly.

### Install Node.js

Node.js LTS is supported.

### Install Dependencies

```
npm install
```

## Run

```
node models/run.js
```
