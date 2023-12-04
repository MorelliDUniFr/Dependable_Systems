#include <stdio.h>
#include <stdlib.h>

#define PLUS '+'
#define MINUS '-'
#define MULTIPLY '*'
#define DIVIDE '/'
#define SQUARE '^'
#define PRIME 'f'
#define FACTORIAL '!'
#define EXIT 'e'
#define ROOT 'r'
#define LOG 'l'

/*@
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
    int res;
    res = a + b;
    return res;
}

/*@
    ensures \result + b == a;
    ensures a - \result == b;
    ensures (a > 0 && b > 0) && a >= b ==> \result >= 0;
    ensures (a > 0 && b > 0) && a <= b ==> \result <= 0;
    ensures (a < 0 && b < 0) && a <= b ==> \result <= 0;
    ensures (a < 0 && b < 0) && a >= b ==> \result >= 0;
    assigns \nothing;
 */
int sub(int a, int b) {
    int res;
    res = a - b;
    return res;
}

/*@
    ensures \result == a * b;
    ensures (a < 0 && b < 0) ==> \result > 0;
    ensures (a > 0 && b < 0) ==> \result < 0;
    ensures (a < 0 && b > 0) ==> \result < 0;
    ensures (a > 0 && b > 0) ==> \result > 0;
    ensures a == 0 || b == 0 ==> \result == 0;
    assigns \nothing;
 */
int mul(int a, int b) {
    int res;
    res = a * b;
    return res;
}

/*@
    requires b != 0;
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
    int res;
    res = a / b;
    return res;
}

/*@
    requires exp >= 0;
    requires base >= 0;
    //ensures \result == base ^ exp;
    ensures exp == 0 ==> \result == 1;
    ensures exp == 1 ==> \result == base;
    assigns \nothing;
 */
int sqr(int base, int exp) {
    int i, res = 1;

    if (exp == 0)
        return 1;
    else if (exp == 1)
        return base;

    /*@
        loop invariant 0 <= i <= exp;
        loop assigns i, res;
        loop variant exp - i;
     */
    for (i = 0; i < exp; ++i)
        res *= base;

    return res;
}

/*@
    requires b >= 0;
    ensures b == 0 ==> \result == 1;
    ensures b == 1 ==> \result == 1;
    assigns \nothing;
 */
int factorial(int b) {
    int a;
    int sum = 1;

    if (b == 0 || b == 1) {
        return 1;
    }

    /*@
        loop invariant 1 <= a <= b + 1;
        loop assigns a, sum;
        loop variant b - a;
     */
    for (a = 1; a <= b; ++a)
        sum *= a;

    return sum;
}

/*@
    requires n > 1;
    ensures \result != NULL;
    assigns \nothing;
*/
int* prime_factorization(int n) {
    int p = 2;
    int* primes = (int*)malloc(20 * sizeof(int));
    int index;

    /*@
        loop invariant n != 1;
        loop invariant 0 <= index <= 19;
        loop assigns n, p, primes[0..19], index;
    */
    for (index = 0; n != 1; ++index) {
        if ((n % p) == 0) {
            n /= p;
            primes[index] = p;
            p = 2;
        } else {
            --index;
            ++p;
        }
    }

    return primes;
}

/*@
    requires radicand >= 0;
    //requires index >= 1;
    //ensures \result >= 0;
    //ensures index == 1 ==> \result == radicand;
    assigns \nothing;
 */
int root(int radicand, int index) {
    int res = radicand / 2;
    double t1 = (1.0 / index);

    /*@
        loop invariant 0 <= i <= 1000;
        loop assigns i, res;
        loop variant 1000 - i;
    */
    for (int i = 0; i < 1000; ++i) {
        res = t1 * ((index - 1.0) * res + radicand / sqr(res, index - 1));
    }

    return res;
}

/*@
    requires base >= 1;
    requires n >= 1;
    ensures \result >= 0;
    assigns \nothing;
 */
int log(int base, int n) {
    int res;

    /*@
        loop invariant n > 0;
        loop assigns n, res;
        loop variant n;
    */
    for (res = 0; n > 0; ++res) {
        n /= base;
    }

    return res - 1;
}

void sel_func(char s) {
    int res = 0;

    switch (s) {
        case PLUS: {
            int a, b;
            printf("Input two numbers : ");
            scanf("%d%d", &a, &b);
            res = add(a, b);
            break;
        }
        case MINUS: {
            int a, b;
            printf("Input two numbers : ");
            scanf("%d%d", &a, &b);
            res = sub(a, b);
            break;
        }
        case MULTIPLY: {
            int a, b;
            printf("Input two numbers : ");
            scanf("%d%d", &a, &b);
            res = mul(a, b);
            break;
        }
        case DIVIDE: {
            int a, b;
            printf("Input two numbers : ");
            scanf("%d%d", &a, &b);
            res = divs(a, b);
            break;
        }
        case SQUARE: {
            int base, exp;
            printf("Input base : ");
            scanf("%d", &base);
            printf("Input exp : ");
            scanf("%d", &exp);
            res = sqr(base, exp);
            break;
        }
        case PRIME: {
            int n = 0;
            while (n < 2) {
                printf("Input a number : ");
                scanf("%d", &n);
            }
            int* myArray = prime_factorization(n);
            int i;

            for (i = 0; i < 19; ++i) {
                if (myArray[i + 1] == 0) {
                    if (i == 0) {
                        printf("Prime number\n");
                        break;
                    } else {
                        break;
                    }
                }
                printf("%d*", myArray[i]);
            }

            if (i != 0) {
                printf("%d\n", myArray[i]);
            }

            free(myArray);
            break;
        }
        case FACTORIAL: {
            int b;
            printf("Input a number : ");
            scanf("%d", &b);
            res = factorial(b);
            break;
        }
        case ROOT: {
            int radicand, index;
            printf("Input radicand : ");
            scanf("%d", &radicand);
            printf("Input index : ");
            scanf("%d", &index);
            res = root(radicand, index);
            break;
        }
        case LOG: {
            int base, n;
            printf("Input base : ");
            scanf("%d", &base);
            printf("Input n : ");
            scanf("%d", &n);
            res = log(base, n);
            break;
        }
        default: {
            printf("Please input again\n");
            break;
        }
    }

    printf("Result = %d\n", res);
}

int main(void) {
    char s;

    while(1) {
        printf("Input a number [ +, -, *, /, ^, root(r), prime factorization(f), !, log(l), exit(e)] : ");
        scanf("%c", &s);

        if(s == EXIT) {
            printf("Bye\n");
            break;
        } else {
            sel_func(s);
        }
    }
}