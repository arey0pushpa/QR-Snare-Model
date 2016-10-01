#include <stdio.h>

#define M 16         
#define N 4


_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[N] vector; 


int  main()
 {    
   vector b1 = 0b0110, b7 = 0b0111 , b5 = 0b0101;
   bitvector bC, bk,b3, b0 = 0b0;
   bitvector b2 = 0b1100000001010000;


   b3 =  (b2 & (1 << b1)) ;
   bC = (b2 & ( 1 << b5));
   bk = (b2 & (1 << b7));
   if(b3 != b0) {
	 printf("hola");
   }

   if(b3 != 0) {

	 printf("shola");
   }


   if ((b2 & (1 << b1))){
	 printf("hi");
   }
   

   assert (0);

 }
