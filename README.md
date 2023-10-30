# Seminar Foundation of Depedable Systems

## Introduction
This repository contains the code for the seminar "Foundation of Depedable Systems" at the University of Fribourg.
The goal of this seminar is to implement a way to detect failures using Hoare Logic.
The repository contains the following folders:
- 'Demo': Contains the code for the demo part of the seminar.
- 'TodoList': Contains the code for the TodoList application.

In order to check the conditions using the Hoare Logic, we need to use the tool 'Frama-C'.

### Mac OS
1. Install homebrew
2. Install required dependencies for Frama-C
```bash
brew install opam gmp
```
3. Install recommended dependencies for Frama-C
```bash
brew install graphviz zmq
```
4. Initialize opam
```bash
opam init --compiler 4.14.1
```
```bash
eval $(opam env)
```

5. Install Frama-C
```bash
opam install frama-c
```


### Windows (WSL)
Since I am using macOS, I have not tested the installation on Windows.
1. Prepare opam installation
```bash
sudo apt update && sudo apt upgrade
```
```bash
sudo apt install make m4 gcc opam
```

2. Opam setup
```bash
opam init --disable-sandboxing --shell-setup
```
```bash
eval $(opam env)
```
```bash
opam install -y opam-depext
```
3. Install Frama-C
```bash
opam depext --install -y frama-c
```

More on the installation on: https://frama-c.com/html/get-frama-c.html

In order to use frama-c, we need to install have alt-ergo on version 2.4.2:
```bash
opam install alt-ergo.2.4.2
```

## Usage
In order to check the conditions using the Hoare Logic, we need to use the tool 'Frama-C'.
The following commands can be used to check the conditions:
```bash
frama-c -wp <file.c>
```

### Demo
The demo part of the seminar is a simple program that divides two numbers.
The program is implemented in the file 'main.c'.

### TodoList
The TodoList application is a simple application that allows the user to add, remove and list tasks.
The application is implemented in the file 'app.c'.

