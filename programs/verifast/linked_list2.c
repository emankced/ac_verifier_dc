#include <stdio.h>
#include <stdlib.h>

struct node {
    struct node* next;
    int data;
};

typedef struct node node;

int main() {
    node* const sixth = malloc(sizeof(node));
    if (sixth == NULL) {
        exit(1);
    }
    sixth->next = NULL;
    sixth->data = 7;

    node* const fifth = malloc(sizeof(node));
    if (fifth == NULL) {
        exit(1);
    }
    fifth->next = sixth;
    fifth->data = 3;

    node* const fourth = malloc(sizeof(node));
    if (fourth == NULL) {
        exit(1);
    }
    fourth->next = fifth;
    fourth->data = 9;

    node* const third = malloc(sizeof(node));
    if (third == NULL) {
        exit(1);
    }
    third->next = fourth;
    third->data = 1;

    node* const second = malloc(sizeof(node));
    if (second == NULL) {
        exit(1);
    }
    second->next = third;
    second->data = 5;

    node* const first = malloc(sizeof(node));
    if (first == NULL) {
        exit(1);
    }
    first->next = second;
    first->data = 6;

    int* const max = malloc(sizeof(int));
    if (max == NULL) {
        exit(1);
    }
    *max = 0;

    node** const next = malloc(sizeof(node*));
    if (next == NULL) {
        exit(1);
    }
    *next = first;

    while (*next != NULL) {
        int const v = (*next)->data;
        if (v > *max) {
            *max = v;
        }
        *next = (*next)->next;
    }

    printf("%d\n", *max);

    free(max);
    *next = first;
    while (*next != NULL) {
        node* addr = *next;
        *next = (*next)->next;
        free(addr);
    }
    free(next);
    return 0;
}
