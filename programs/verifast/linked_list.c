#include <stdio.h>
#include <stdlib.h>

int main() {
    void* const sixth = malloc(sizeof(int*) + sizeof(int));
    if (sixth == NULL) {
        exit(1);
    }
    void** const sixth_next = sixth;
    int* const sixth_value = (int*) (sixth_next + 1);
    *sixth_next = NULL;
    *sixth_value = 7;

    void* const fifth = malloc(sizeof(int*) + sizeof(int));
    if (fifth == NULL) {
        exit(1);
    }
    void** const fifth_next = fifth;
    int* const fifth_value = (int*) (fifth_next + 1);
    *fifth_next = sixth;
    *fifth_value = 3;

    void* const fourth = malloc(sizeof(int*) + sizeof(int));
    if (fourth == NULL) {
        exit(1);
    }
    void** const fourth_next = fourth;
    int* const fourth_value = (int*) (fourth_next + 1);
    *fourth_next = fifth;
    *fourth_value = 9;

    void* const third = malloc(sizeof(int*) + sizeof(int));
    if (third == NULL) {
        exit(1);
    }
    void** const third_next = third;
    int* const third_value = (int*) (third_next + 1);
    *third_next = fourth;
    *third_value = 1;

    void* const second = malloc(sizeof(int*) + sizeof(int));
    if (second == NULL) {
        exit(1);
    }
    void** const second_next = second;
    int* const second_value = (int*) (second_next + 1);
    *second_next = third;
    *second_value = 5;

    void* const first = malloc(sizeof(int*) + sizeof(int));
    if (first == NULL) {
        exit(1);
    }
    void** const first_next = first;
    int* const first_value = (int*) (first_next + 1);
    *first_next = second;
    *first_value = 6;

    int* const max = malloc(sizeof(int));
    if (max == NULL) {
        exit(1);
    }
    *max = 0;

    void*** const next = malloc(sizeof(void*));
    if (next == NULL) {
        exit(1);
    }
    *next = first;

    while (*next != NULL) {
        int const v = *((int*) (*next + 1));
        if (v > *max) {
            *max = v;
        }
        *next = **next;
    }

    printf("%d\n", *max);

    free(max);
    *next = first;
    while (*next != NULL) {
        void* addr = *next;
        *next = **next;
        free(addr);
    }
    free(next);
    return 0;
}
