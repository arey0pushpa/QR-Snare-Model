#include<stdio.h>

#define M 2
#define N 4

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector;
typedef unsigned __CPROVER_bitvector[N] bigvector;


void main() {

 bitvector b1, b3;
 bigvector b2;
 b1 = 0b11;
 b2 = (b1 << 2);

 assert(0);

}


