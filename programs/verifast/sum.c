#include <stdio.h>
#include <stdlib.h>

int main()
//@ requires true;
//@ ensures true;
{
    int* const sum = malloc(sizeof(int));
    if (sum == NULL) {
        exit(1);
    }
    *sum = 0;
    //@ open integer(sum, 0);

    int const size = 6;
    int* const list = malloc(sizeof(int) * size);
    if (list == NULL) {
        exit(1);
    }
    *list = 15;
    *(list+1) = 3;
    *(list+2) = 7;
    *(list+3) = 10;
    *(list+4) = 2;
    *(list+5) = 5;
    //@ open ints(list, size, cons(15, cons(3, cons(7, cons(10, cons(2, cons(5, nil)))))));

    for (int i = 0; i < size; ++i)
    //@ invariant integer(sum, _) &*& ints(list, size, cons(15, cons(3, cons(7, cons(10, cons(2, cons(5, nil))))))) &*& 0 <= i &*& i <= size;
    {
        // *(list+i) is not possible to use...
        *sum += list[i];
    }

    printf("%d\n", *sum);

    //@ close integer(sum, _); // cannot prove value 42...
    free(sum);
    //@ close ints(list, size, cons(15, cons(3, cons(7, cons(10, cons(2, cons(5, nil)))))));
    free(list);
    return 0;
}
