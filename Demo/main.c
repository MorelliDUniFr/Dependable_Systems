#include <assert.h>
#include <stdio.h>

// use the following command to compile the program
//frama-c -wp main.c

/* Frama-C is an open-source software analysis framework designed for the verification and analysis of C and C++ code.
 * It provides a platform for applying formal methods and program analysis techniques to improve the reliability,
 * safety, and security of software written in these programming languages. Frama-C allows developers to perform
 * various types of analysis, including static analysis, formal verification, and runtime error detection, to ensure
 * that code behaves correctly and to identify potential issues early in the development process. It is particularly
 * valuable for safety-critical and high-assurance software applications.
 */

/*@
  requires y != 0; // Ensure y is not zero
  assigns \nothing; // This function does not modify any memory locations
  ensures \result * y == x; // Ensure the result is correct
*/
int safe_divide(int x, int y) {
    return x / y;
}

/*@
    assigns \nothing; // means that the function does not modify any memory locations.
 */
int main() {
    int x = 10;
    int y = 2;
    int result;

    // Ensure the pre-conditions are satisfied
    //@ assert(y != 0);
    assert(y != 0);

    // Call the division function
    result = safe_divide(x, y);

    // Ensure the post-condition is satisfied
    //@ assert(result * y == x);
    assert(result * y == x);

    return 0;
}



