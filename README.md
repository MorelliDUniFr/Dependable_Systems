# Seminar Foundation of Depedable Systems

## Introduction
This repository contains the code for the seminar "Foundation of Depedable Systems" at the University of Fribourg.
The goal of this seminar is to implement a way to detect failures using Hoare Logic.
The repository contains the following folders:
- 'Demo': Contains the code for the demo part of the seminar.
- 'TodoList': Contains the code for the TodoList application.
- 'Calculator': Contains the code for the Calculator application.

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

Certain functions, like printf() or scanf(), are not supported by the tool, and give a lot of warnings.
In order to ignore these warnings, we can use the following command:
```bash
// frama-c -wp -wp-skip-fct <list of functions to avoid> <file.c>
```

In this case, we can ignore the following functions:
```bash
frama-c -wp -wp-skip-fct "myprintf, myscanf" New_Calculator.c
```

If we want also to include the runtime errors, we can use the following command:
```bash
frama-c -wp -wp-rte <file.c>
```

In this case, we can use the following command:
```bash
frama-c -wp -wp-rte -wp-skip-fct "myprintf, myscanf" New_Calculator.c
```

### Demo
The demo part of the seminar is a simple program that divides two numbers.
The program is implemented in the file 'main.c'.

### TodoList
The TodoList application is a simple application that allows the user to add, remove and list tasks.
The application is implemented in the file 'app.c'.

### Calculator
The Calculator application is a simple application that allows the user to do the basic operations.

## Comments
This section contains the comments for the code.
Things like the errors found in the logic of the code thanks to the Hoare Logic, workarounds used in the code, etc.

### Logical errors found in the code
Thanks to the Hoare Logic and the runtime error detection, I found the following logical errors in the code:
- requires (a + b) <= INT_MAX;
  requires (a + b) >= INT_MIN;
- requires (a - b) <= INT_MAX;
  requires (a - b) >= INT_MIN;

There were no bounds on the variables, so the result of the operations could be out of the range of the integer type.
The solution is quite simple: we need to check if the result of the operation is in the range of the integer type.
If the result is not in the range, we can print an error message and exit the program.
```
case PLUS: {
  signed int a, b;
  myprintf("Input two numbers : ");
  myscanf("%d%d", &a, &b);
  if (a + b <= INT_MAX && a + b >= INT_MIN) {
    res = add(a, b);
  } else {
    myprintf("Overflow\n");
    return;
  }
  break;
}
```

### Workarounds used in the code
#### Printf and scanf
Frama-C and the wp plugin are very useful tools to check the conditions of a program or function that we wrote ourselves.
The problem lies in the fact that if a function is not implemented by us, we cannot check the conditions of that function.
In the case of this project, mainly two functions that are used in the code are not implemented by us: 
- printf()
- scanf().

In order to partially solve this problem, we have to create our own functions that do the same thing as the original functions:
- myprintf()
- myscanf().

These functions do the exact same thing as the original functions, but they are implemented by us, so we can exclude them in 
the wp plugin.

#### Overflow of the variables
There are some runtime errors founds, mainly because of the overflow of the variables.
In order to solve the problem, we can check if the variables are in the range of the type of the variable.
For example, if we have an integer, we can check if the integer is in the range of the integer type.
If the integer is not in the range, we can print an error message and exit the program.
But this is not always the case, for example if we have a power function, we cannot check if the result of the power is in the range of the integer type.
So we need to use some tricks to solve the problem: in the case of the power function, 
we can fix the maximum values of the base and the exponent, so we can check if the result is in the range of the integer type.
In this case we can use the following values:
- base <= 12
- exponent <= 7
The same applies to the factorial function:
- factorial <= 12

### Things not yet implemented by frama-c and the wp plugin
Multiple things are not yet implemented by the wp plugin:
- Dynamic memory allocation
- Dynamic memory deallocation
So we cannot check the conditions of the functions that use dynamic memory allocation or deallocation.

### Things not checked by me
Out of the 273 goals, 15 are not successful:
1. power_assert_rte_signed_overflow_2 & power_assert_rte_signed_overflow: I fixed the overflow problem, but the runtime error is still there.
2. factorial_assert_rte_signed_overflow & factorial_assert_rte_signed_overflow_2: The same thing applies here.
3. prime_factorization_assert_rte_signed_overflow_3: Also the same things applies here. 
4. root_assert_rte_signed_overflow_2: The overflow has been taken on account, but the runtime error is still there. 
5. sel_func_assert_rte_signed_overflow_2 & sel_func_assert_rte_signed_overflow & sel_func_assert_rte_signed_overflow_5 & sel_func_assert_rte_signed_overflow_6 & sel_func_assert_rte_signed_overflow_9 & sel_func_assert_rte_signed_overflow_10: The same thing applies here. 
6. sel_func_assert_rte_division_by_zero: Normally all the division by zero are checked. 
7. sel_func_assigns_exit_part07: This problem is tied to the fact that we allocate memory dynamically, but is freed just after. 
8. sel_func_assigns_normal_part07: The same thing applies here.
