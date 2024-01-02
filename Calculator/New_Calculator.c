#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <limits.h>

#define PLUS '+'
#define MINUS '-'
#define MULTIPLY '*'
#define DIVIDE '/'
#define POW 'p'
#define PRIME 'f'
#define FACTORIAL '!'
#define EXIT 'e'
#define ROOT 'r'
#define LOG 'l'

// Auxiliary functions
/*@
    assigns \nothing;
 */
void myprintf(const char* format, ...) {
    va_list args;
    va_start(args, format);
    vprintf(format, args);
    va_end(args);
}

/*@
    assigns \nothing;
 */
void myscanf(const char* format, ...) {
    va_list args;
    va_start(args, format);
    vscanf(format, args);
    va_end(args);
}

/*@
    requires (a + b) <= INT_MAX;
    requires (a + b) >= INT_MIN;
    ensures \result - b == a;
    ensures \result - a == b;
    ensures (a < 0 && b < 0) ==> \result < 0;
    ensures (a > 0 && b < 0) && a >= -b ==> \result >= 0;
    ensures (a > 0 && b < 0) && a <= -b ==> \result <= 0;
    ensures (a < 0 && b > 0) && -a >= b ==> \result <= 0;
    ensures (a < 0 && b > 0) && -a <= b ==> \result >= 0;
    assigns \nothing;
 */
int add(int a, int b) {
    signed int res;
    res = a + b;
    return res;
}

/*@
    requires (a - b) <= INT_MAX;
    requires (a - b) >= INT_MIN;
    ensures \result + b == a;
    ensures a - \result == b;
    ensures (a > 0 && b > 0) && a >= b ==> \result >= 0;
    ensures (a > 0 && b > 0) && a <= b ==> \result <= 0;
    ensures (a < 0 && b < 0) && a <= b ==> \result <= 0;
    ensures (a < 0 && b < 0) && a >= b ==> \result >= 0;
    assigns \nothing;
 */
int sub(int a, int b) {
    signed int res;
    res = a - b;
    return res;
}

/*@
    requires (a * b) <= INT_MAX;
    requires (a * b) >= INT_MIN;
    ensures \result == a * b;
    ensures (a < 0 && b < 0) ==> \result > 0;
    ensures (a > 0 && b < 0) ==> \result < 0;
    ensures (a < 0 && b > 0) ==> \result < 0;
    ensures (a > 0 && b > 0) ==> \result > 0;
    ensures a == 0 || b == 0 ==> \result == 0;
    assigns \nothing;
 */
int mul(int a, int b) {
    signed int res;
    res = a * b;
    return res;
}

/*@
    requires b != 0;
    requires (a / b) <= INT_MAX;
    requires (a / b) >= INT_MIN;
    ensures \result == a / b;
    ensures (a < 0 && b < 0) && a >= b ==> \result >= 0 && \result <= 1;
    ensures (a < 0 && b < 0) && a <= b ==> \result >= 1;
    ensures (a > 0 && b < 0) && a >= -b ==> \result <= -1;
    ensures (a > 0 && b < 0) && a <= -b ==> \result >= -1 && \result <= 0;
    ensures (a < 0 && b > 0) && -a >= b ==> \result <= -1;
    ensures (a < 0 && b > 0) && -a <= b ==> \result <= 0 && \result >= -1;
    ensures (a > 0 && b > 0) && a >= b ==> \result >= 1;
    ensures (a > 0 && b > 0) && a <= b ==> \result <= 1 && \result >= 0;
    ensures a == b ==> \result == 1;
    ensures a == 0 ==> \result == 0;
    assigns \nothing;
 */

int divs(int a, int b) {
    signed int res;
    res = a / b;
    return res;
}

/*@
    requires 0 <= exp <= 7;
    requires 0 <= base <= 21;
    requires base != 0 || exp != 0;
    ensures exp == 0 ==> \result == 1;
    ensures exp == 1 ==> \result == base;
    ensures base == 0 && exp > 0 ==> \result == 0;
    ensures \result <= INT_MAX;
    assigns \nothing;
 */
int power(int base, int exp) {
    signed int i, res = 1;

    if (exp == 0) {
        return 1;
    } else if (exp == 1) {
        return base;
    }
    //@ assert exp > 1;
    if (base == 0) {
        return 0;
    }
    //@ assert base > 0;

    /*@
        loop invariant 0 <= i <= exp;
        loop invariant res <= INT_MAX;
        loop invariant res >= INT_MIN;
        loop assigns i, res;
        loop variant exp - i;
     */
    for (i = 0; i < exp; ++i) {
        res *= base;
    }

    return res;
}

/*@
    requires 0 <= b <= 12;
    ensures b == 0 ==> \result == 1;
    ensures b == 1 ==> \result == 1;
    ensures \forall integer i; 0 <= i <= 12 ==> \result <= INT_MAX;
    ensures \result <= INT_MAX;
    assigns \nothing;
 */
int factorial(int b) {
    signed int sum = 1;

    if (b == 0 || b == 1) {
        return 1;
    }
    //@ assert b > 1;

    /*@
        loop invariant 1 <= a <= b + 1;
        loop invariant INT_MIN <= sum <= INT_MAX;
        loop assigns a, sum;
        loop variant b - a;
     */
    for (int a = 1; a <= b; ++a) {
        sum *= a;
    }
    return sum;
}

/*@
    requires n > 1;
    requires n <= INT_MAX;
    requires \valid(primes + (0..19));
    assigns primes[0..19];
*/
void prime_factorization(int n, int* primes) {
    signed int p = 2;
    signed int index = 0;
    //@ assert index == 0;

    /*@
        loop invariant n >= 1;
        loop invariant p >= 2;
        loop invariant \forall integer i; 0 <= i < index ==> primes[i] != 0;
        loop invariant 0 <= index <= 19;
        loop invariant \valid(primes + (0..19));
        loop assigns n, p, index, primes[0..19];
    */
    while(n != 1 || index <= 19) {
        if ((n % p) == 0) {
            //@ assert n % p == 0;
            //@ assert p != 0;
            n /= p;
            //@ assert \valid(primes + (0..19));
            primes[index] = p;
            if (index < 19) {
                ++index;
            }
            p = 2;
        } else {
            //@ assert n % p != 0;
            ++p;
            //@ assert p >= 2;
            //@ assert p <= INT_MAX;
        }
    }
    //@ assert n == 1;
    //@ assert \forall integer i; 0 <= i < index ==> primes[i] != 0;
}

/*@
    requires radicand >= 0;
    requires radicand <= INT_MAX;
    ensures \result >= 0;
    ensures \result <= INT_MAX;
    assigns \nothing;
 */
int root(int radicand) {
    signed int res = 0;

    /*@
        loop invariant 0 <= i <= radicand/2;
        loop invariant res*res <= radicand;
        loop invariant res >= 0;
        loop assigns i, res;
        loop variant radicand/2 - i;
    */
    for (int i = 0; i < radicand/2; ++i) {
        if (i*i >= radicand) {
            if (i*i == radicand) {
                res = i;
            } else {
                res = i - 1;
            }
            break;
        }
    }

    return res;
}

/*@
    requires base >= 1;
    requires base <= INT_MAX;
    requires n >= 1;
    requires n <= INT_MAX;
    ensures \result >= 0;
    assigns \nothing;
 */
int logs(int base, int n) {
    int res;

    if (n < base) {
        return 0;
    }
    //@ assert n >= base;

    /*@
        loop invariant n > 0;
        loop invariant 0 <= res <= 1000;
        loop assigns n, res;
        loop variant 1000 - res;
    */
    for (res = 0; res < 1000; ++res) {
        n /= base;

        if (n <= 1) {
           break;
        }
    }

    return res + 1;
}
/*@
    requires s == PLUS || s == MINUS || s == MULTIPLY || s == DIVIDE || s == POW || s == PRIME || s == FACTORIAL || s == ROOT || s == LOG;
    assigns \nothing;
 */
void sel_func(char s) {
    int res = 0;

    switch (s) {
        case PLUS: {
            int a, b;
            myprintf("Input two numbers : ");
            myscanf("%d%d", &a, &b);
            if (a + b > INT_MAX || a + b < INT_MIN) {
                myprintf("Overflow1\n");
                return;
            }
            //@ assert a + b <= INT_MAX;
            //@ assert a + b >= INT_MIN;

            res = add(a, b);
            break;
        }
        case MINUS: {
            int a, b;
            myprintf("Input two numbers : ");
            myscanf("%d%d", &a, &b);
            if (a - b > INT_MAX || a - b < INT_MIN) {
                myprintf("Overflow\n");
                return;
            }
            //@ assert a - b <= INT_MAX;
            //@ assert a - b >= INT_MIN;

            res = sub(a, b);
            break;
        }
        case MULTIPLY: {
            int a, b;
            myprintf("Input two numbers : ");
            myscanf("%d%d", &a, &b);
            if (a >= INT_MAX / b || a <= INT_MIN / b) {
                myprintf("Overflow\n");
                return;
            }
            //@ assert a * b <= INT_MAX;
            //@ assert a * b >= INT_MIN;
            res = mul(a, b);
            break;
        }
        case DIVIDE: {
            int a, b;
            myprintf("Input two numbers : ");
            myscanf("%d%d", &a, &b);
            if (b == 0) {
                myprintf("Divide by zero\n");
                return;
            }
            if (b != 0 && ((a / b > INT_MAX) || (a / b < INT_MIN))) {
                myprintf("Overflow\n");
                return;
            }
            //@ assert a / b <= INT_MAX;
            //@ assert a / b >= INT_MIN;
            //@ assert b != 0;
            res = divs(a, b);
            break;
        }
        case POW: {
            int base, exp;
            myprintf("Input base : ");
            myscanf("%d", &base);
            if (base < 0) {
                myprintf("Input base >= 0\n");
                return;
            }
            myprintf("Input exp : ");
            myscanf("%d", &exp);
            if (base == 0 && exp == 0) {
                myprintf("0^0 is undefined\n");
                return;
            }
            if (exp < 0) {
                myprintf("Input exp >= 0\n");
                return;
            }
            if (base > 21 || exp > 7) {
                myprintf("Overflow\n");
                return;
            }
            //@ assert base <= 21;
            //@ assert exp <= 7;
            //@ assert base >= 0;
            //@ assert exp >= 0;
            //@ assert base != 0 || exp != 0;

            res = power(base, exp);
            break;
        }
        case PRIME: {
            int n = 0;
            //@ allocates primes;
            int* primes = (int*)malloc(20 * sizeof(int));

            /*@
                loop invariant n < 2;
                loop assigns n;
             */
            while (n < 2) {
                myprintf("Input a number : ");
                myscanf("%d", &n);
            }
            //@ assert n >= 2;
            if (n > INT_MAX) {
                myprintf("Input a number <= INT_MAX\n");
                return;
            }
            prime_factorization(n, primes);
            int i;

            if (primes[1] == 0) {
                myprintf("Prime number\n");
                //@ frees primes;
                free(primes);
                return;
            } else {
                myprintf("Prime factorization : ");
            }

            /*@
                loop invariant 0 <= i <= 19;
                loop assigns i;
                loop variant 19 - i;
             */
            for (i = 0; i < 19; ++i) {
                if (primes[i + 1] == 0) {
                    break;
                }
                myprintf("%d*", primes[i]);
            }

            if (i != 0) {
                myprintf("%d\n", primes[i]);
            }

            //@ frees primes;
            free(primes);
            return;
        }
        case FACTORIAL: {
            int b;
            myprintf("Input a number : ");
            myscanf("%d", &b);
            if (b < 0 || b > 12) {
                myprintf("Input a number 0 <= n <= 12\n");
                return;
            }
            //@ assert b >= 0;
            //@ assert b <= 12;
            res = factorial(b);
            break;
        }
        case ROOT: {
            int radicand;
            myprintf("Input radicand : ");
            myscanf("%d", &radicand);
            if (radicand < 0) {
                myprintf("Input radicand >= 0\n");
                return;
            }
            if (radicand > INT_MAX) {
                myprintf("Input radicand <= INT_MAX\n");
                return;
            }
            //@ assert radicand >= 0;
            //@ assert radicand <= INT_MAX;
            res = root(radicand);
            break;
        }
        case LOG: {
            int base, n;
            myprintf("Input base : ");
            myscanf("%d", &base);
            if (base < 1 || base > INT_MAX) {
                myprintf("Input base >= 1\n");
                return;
            }
            myprintf("Input n : ");
            myscanf("%d", &n);
            if (n < 1 || n > INT_MAX) {
                myprintf("Input n >= 1\n");
                return;
            }
            //@ assert base >= 1;
            //@ assert n >= 1;
            //@ assert base <= INT_MAX;
            //@ assert n <= INT_MAX;
            //@ assert base != 0;
            res = logs(base, n);
            break;
        }
        default: {
            myprintf("Please input again\n");
            break;
        }
    }

    myprintf("Result = %d\n", res);
}

/*@
    assigns \nothing;
 */
int main(void) {
    char s;

    /*@
        loop assigns s;
        loop invariant \true;
     */
    while(1) {
        myprintf("Input a command [+, -, *, /, ^, root(r), prime factorization(f), !, log(l), exit(e)] : ");
        myscanf(" %c", &s);

        if(s == EXIT) {
            //@ assert s == EXIT;
            myprintf("Bye\n");
            break;
        } else {
            if (s != PLUS && s != MINUS && s != MULTIPLY && s != DIVIDE && s != POW && s != PRIME && s != FACTORIAL && s != ROOT && s != LOG) {
                myprintf("Please input again\n");
                continue;
            } else {
                //@ assert s != EXIT;
                sel_func(s);
            }
        }
    }
}