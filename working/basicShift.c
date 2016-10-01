
#include <stdlib.h>

#define M 2         
#define N 4
_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[N] bigvector; 


void main() {
 
    bitvector b1, b2, b3;
    bigvector V1 , V2;

    b1 = 0b01;
    b2 = 0b11;

    V1 =  ((b1 << M) | b2 );    
    V2 =  ((b2 << M) | b1);

    assert(0);
}
