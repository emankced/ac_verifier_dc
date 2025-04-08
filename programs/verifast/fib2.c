#include <stdio.h>
#include <stdlib.h>

int main()
//@ requires true;
//@ ensures true;
{
    int* const n = malloc(sizeof(int));
    if (n == NULL) {
        exit(1);
    }

    *n = 10;
    //@ open integer(n, 10);

    int* const fib = malloc(sizeof(int) * 2);
    if (fib == NULL) {
        exit(1);
    }
    *fib = 0;
    //@ open integer(fib, 0);

    int* const fib2 = fib+1;
    *fib2 = 1;
    //@ open integer(fib2, 1);

    while (*n > 0)
    // invariant *n |-> ?vn &*& 0 <= vn &*& ints(fib, 2, cons(?vx, cons(?vy, nil)));
    //@ invariant *n |-> ?vn &*& 0 <= vn &*& *fib |-> ?vx &*& *fib2 |-> ?vy;
    {
        *n = *n - 1;
        int x = *fib + *fib2;
        *fib2 = *fib;
        *fib = x;
    }

    printf("%d\n", *fib);

    //@ close ints(fib, 2, _);
    free(fib);
    //@ close integer(n, 0);
    free(n);
    return 0;
}
