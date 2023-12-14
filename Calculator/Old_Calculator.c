#include <stdio.h>

void add() {
    int a, b;

    printf("Input two numbers : ");
    scanf("%d%d", &a, &b);
    printf("Result = %d\n", a + b);
}

void sub() {
    int a, b;

    printf("Input two numbers : ");
    scanf("%d%d", &a, &b);
    printf("Result = %d\n", a - b);
}

void mul() {
    int a, b;

    printf("Input two numbers : ");
    scanf("%d%d", &a, &b);
    printf("Result = %d\n", a * b);
}

void divs() {
    int a, b;

    printf("Input two numbers : ");
    scanf("%d%d", &a, &b);
    printf("Result = %d\n", a / b);
}

void power() {
    int exp, base, i;
    int result = 1;

    printf("Input base : ");
    scanf("%d", &base);
    printf("Input exp : ");
    scanf("%d", &exp);

    for (i = 0; i < exp; ++i)
        result *= base;

    printf("%d^%d = %d\n",
           base, exp, result);
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

void factorial() {
    int a, b;
    int sum = 1;

    printf("Input a number : ");
    scanf("%d", &b);

    for (a = 1; a <= b; ++a)
        sum *= a;

    printf("%d!=%d\n", b, sum);
}

void sel_func(int s) {
    switch (s) {
        case 1: {
            add();
            break;
        }
        case 2: {
            sub();
            break;
        }
        case 3: {
            mul();
            break;
        }
        case 4: {
            divs();
            break;
        }
        case 5: {
            power();
            break;
        }
        case 6: {
            prime_factorization();
            break;
        }
        case 7: {
            factorial();
            break;
        }
    }
}

int main(void) {
    char s;

    while(1) {
        printf("Input a number [ +, -, *, /, ^, root(r), prime factorization(f), !, log(l), exit(e)] : ");
        scanf("%c", &s);

        if(s == 'e') {
            printf("Bye\n");
            break;
        } else {
            sel_func(s);
        }
    }
}
