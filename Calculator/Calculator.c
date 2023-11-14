#include <stdio.h>

const char PLUS = '+';
const char MINUS = '-';
const char MULTIPLY = '*';
const char DIVIDE = '/';
const char SQUARE = '^';
const char PRIME = 'f';
const char FACTORIAL = '!';
const char EXIT = 'e';
const char ROOT = 'r';
const char LOG = 'l';

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
int div(int a, int b) {
    int res;
    res = a / b;
    return res;
}

/*@
    requires exp >= 0;
    requires base >= 0;
    //ensures \result == base ^ exp;
    ensures exp == 0 ==> \result == 1;
    //ensures exp == 1 ==> \result == base;
    //ensures (exp % 2) == 0 ==> \result > 0;
    //ensures (exp % 2) == 1 ==> \result < 0;
    assigns \nothing;
 */
int sqr(int base, int exp) {
    int i, res = 1;

    for (i = 0; i < exp; ++i)
        res *= base;

    return res;
}



void prime_factorization() {
    int n = 0;
    while (n < 2) {
        printf("Input a number : ");
        scanf("%d", &n);
    }

    int p = 2;
    int primes[20];
    int index = 0;
    int i;

    while (1 != n) {
        if (0 == (n % p)) {
            n = n / p;
            primes[index] = p;
            ++index;
            p = 2;
        } else {
            ++p;
        }
    }

    if (1 == index) {
        printf("Prime number\n");
    } else {
        for (i = 0; i < index - 1; ++i)
            printf("%d*", primes[i]);

        printf("%d\n", primes[i]);
    }
}

int factorial(int b) {
    int a;
    int sum = 1;

    for (a = 1; a <= b; ++a)
        sum *= a;

    return sum;
}

int root(int radicand, int index) {
    int res = radicand / 2;

    for (int i = 0; i < 1000; ++i) {
        res = (1 / index) * ((index - 1) * res + radicand / sqr(res, index - 1));
    }

    return res;
}

int log(int base, int n) {
    int res = 0;

    while (n > 0) {
        n /= base;
        res++;
    }

    res--;

    return res;
}

void sel_func(char s) {
    int res = 0;
    printf("Selected : %c\n", s);

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
            res = div(a, b);
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
            prime_factorization();
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

        printf("s = %c\n", s);

        if(s == 'e') {
            printf("Bye\n");
            break;
        } else {
            sel_func(s);
        }
    }
}
