/* Complete Spec implementation of the V Snare - T Snare MOdel
   Github Link
*/

// --------------------------------------- TESTED ---------------------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>


#define M 4         
#define N 2
#define snareLength 4
#define len 2 

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 

unsigned int  nondet (){  
  unsigned int num = nondet_uint();
  __CPROVER_assume( num>= 0 && num  <= 1);
   return num;
};

unsigned int zeroTon(unsigned int n) {
    unsigned int result = nondet_uint();
    __CPROVER_assume(result >=0 && result <=n);
    return result ;
};

struct EdgeBag
 {
   unsigned int ith;
   unsigned int jth;
   unsigned int count;
   unsigned int count2;
   bitvector edgeWeight;
   snareVector zebra[snareLength];
   snareVector zebra2[snareLength];
   snareVector  vSnare;
   snareVector tSnare;
   snareVector combinedMask; 
   snareVector combinedMask2; 
};

// ------------------------------------------------ TESTED ---------------------------------------------------------

int  main()
 
 {    

    unsigned int pos, i, j, k, l, w, x, y , iVal, jVal, g, g0, gl, lastg, ng, nl, nl2 ;
    unsigned int edgePos = 0, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp, result;
    unsigned int  ticks, ticks2, valj, vali , calc;
    unsigned int connectedArray[N] = {}, edgeCount = 0;
    _Bool Ck=0, Cl = 0,Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5, C6 , C7; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, centTotal2, placeHolder, v, vl, vl2, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] , fComp , bComp;    
    snareVector friendMatrix[snareLength];     
    snareVector onOffMatrix[N], stCorres;
  
    unsigned int graph[N][N]; 

	edgeCount = 0;
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
			if(i != j) {
				__CPROVER_assume(graph[i][j] >= 0 && graph[i][j] <=2);
			    if (graph[i][j] == 1)
                    edgeCount += 1;	
                else if (graph[i][j] == 2) 
					edgeCount += 2;

            }
             else  
				__CPROVER_assume(graph[i][j] == 0); 

			} 
    }


     __CPROVER_assume(edgeCount == len);

   

    //  Define the Container as Basis of our work  --------------------------
     struct EdgeBag edgeBag[len];
     //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
     edgePos = 0;
     for  (i = 0; i < N; i++) {
             for  (j = 0; j < N; j++) {
               if ((graph[i][j] == 1) || (graph[i][j] == 2)) {
                   edgeBag[edgePos].ith = i;     // Record the source node
                   edgeBag[edgePos].jth = j;     // Record the target Node
 
                   // Only molecule present at the nodes are allowed to fly out.
                   __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                   __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0); ;
 
                   // Additional Vedge[i][j] and Tedge[i][j] is used to be lookup value in global steady state check condition.
                   Vedge[i][j] = edgeBag[edgePos].vSnare;
                   Tedge[i][j] = edgeBag[edgePos].tSnare;
                   edgePos = edgePos + 1;
             }
 
             if ((graph[i][j] == 2)) {
                  edgeBag[edgePos].ith = i;      // Record the Source Node  
                  edgeBag[edgePos].jth = j;      // Record the Target Node
 
                 // Only molecule present at the nodes are allowed to fly out.
                   __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                   __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0);
                    // Additional Vedge2[i][j] and Tedge2[i][j] is used to be lookup value in global steady state check condition.
                   Vedge2[i][j] = edgeBag[edgePos].vSnare;
                   Tedge2[i][j] = edgeBag[edgePos].tSnare;
                   edgePos = edgePos + 1;
             }

          }
     }
   /*  
         C4 = 0;
         for ( i = 0; i < N ; i++) {
             calc = 0;
             for ( j = 0 ; j < len; j++) {              
                if ( (edgeBag[j].ith == i) || (edgeBag[j].jth == i) ){
                     calc = calc + 1;
                }
               }
             __CPROVER_assume(calc >= 3);
             if(calc < 4) {
                 C4 = 1;
             }
         }
    C0 = 1; 
    
	for (j = 0; j < len; j++) {   
         C0 = (C0 && (edgeBag[j].vSnare != 0));
         C0 = (C0 && (edgeBag[j].tSnare != 0));
     }

    for ( i = 0; i < N; i++) {
              __CPROVER_assume(Vnodes[i] != 0);
    }
     */
    C1 = 1;
// No.1 : Steady State Condition For VSnares	
   for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                // If there is a back edge from taget to source we are done.
                if (((graph[valj][vali] >= 1) && (Vedge[valj][vali] & (1 << j) )) || ((graph[valj][vali] == 2) && (Vedge2[valj][vali] & (1 << j)  )) )   {
                      C1 = C1 && 1;
                }
                // Else continue checking for the cycle
                else { 
         		// g0 is unsigned int checks if there is an edge btw two nodes
                //  It should be on some cycle, So assume that it'll be between 0 and N-2
                //  As we are Only considering elementary cycles.
                unsigned int big;
                __CPROVER_assume( big >= 1 && big <= (N - 2));
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
	            g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	            v0  = Vedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
                v2  = Vedge2[valj][path[0]];
               
                gl  = graph[path[big - 1]][vali];
	            vl  = Vedge[path[big - 1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
                vl2 = Vedge2[path[big - 1]][vali];

               if ( ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & (1 << j)) || ( v2 & (1 << j)) ) )) &&  ((( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }
           
           
           if ( big > 1 ) {
               for (k = 0; k < big - 1 ; k++)  {                  // Dynamic 				    	 
		           ng  = graph[path[k]][path[k+1]];
		           nv  = Vedge[path[k]][path[k+1]];
		           nv2 = Vedge2[path[k]][path[k+1]];	
                   if ( ((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j)))) ) {
                           C1 = C1 && 1;
                   }
                   else {
                           C1 = 0;
                   }
               }
           }


           }  // else Outside closed
        }  // If closed
      }  // jth for closed    
    }   //  ith for closed 
  
  
  
// No.2 : Steady State Condition For VSnares	
   for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           if(edgeBag[i].tSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                
                if (((graph[valj][vali] >= 1) && (Tedge[valj][vali] & (1 << j) ))  || ((graph[valj][vali] == 2) && (Tedge2[valj][vali] & (1 << j) )))  {
                      C1 = C1 && 1;
                 }

                else { 
         		// g0 is unsigned int checks if there is an edge btw two nodes
                //  It should be on some cycle, So assume that it'll be between 0 and N-2
                //  As we are Only considering elementary cycles.
                unsigned int big;
                __CPROVER_assume( big >= 1 && big <= (N - 2));
     
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
    	        g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	            v0  = Tedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
                v2  = Tedge2[valj][path[0]];
               
                gl  = graph[path[big - 1]][vali];
	            vl  = Tedge[path[big - 1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
                vl2 = Tedge2[path[big - 1]][vali];

               if ( ((( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v2 & (1 << j)) ) )) &&  ((( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }
          if ( big > 1) {
               for (k = 0; k < big - 1 ; k++)  {                  // Dynamic 				    	 
		           ng  = graph[path[k]][path[k+1]];
		           nv  = Tedge[path[k]][path[k+1]];
		           nv2 = Tedge2[path[k]][path[k+1]];	
                   if (((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))) )) {
                           C1 = C1 && 1;
                   }
                   else {
                           C1 = 0;
                   }
               }
          }
           }  // else Outside closed
        } 
      }  // jth for closed    
    }   


    for  (i = 0; i < len; i++) {
        centTotal = 0b0;
        centTotal2 = 0b0;

        total = 0b0;
        ticks = 0;
        ticks2 = 0;
        Ck = 0;
        Cl = 0;
        
        //  Check if jth vSnare is present then check if all its t-snare frds are present on the edge. 
        //  If yes don't consider him as a cnadidate to check the fusion that happens btw current nodes.

      // For each of the vsnares presentc on the edge you ahve t do 
        for  (j = 0; j < snareLength; j++) {
           v = edgeBag[i].vSnare;
           t = edgeBag[i].tSnare;
           f = friendMatrix[j];
           valj = edgeBag[i].jth;
           vali = edgeBag[i].ith;
          
           if( (v & (1 << j)) && ((t & f) != f) ){
              edgeBag[i].zebra[ticks] = f;
              centTotal = centTotal | f;
              ticks = ticks + 1;     
              if ( (((Tnodes[valj]) & f)  == f)  &&  (((Tnodes[vali]) & f) != f)) {
                 Ck = Ck || 1;                                  
              }
           }
         }

         edgeBag[i].combinedMask = centTotal;
         edgeBag[i].count = ticks;

       
       // For each of the vsnare presnet at the target compartment and trying to find the fusion via backroot
        /*----------------------------------------------*/
      for  (j = 0; j < snareLength; j++) {
           v = edgeBag[i].vSnare;
           t = edgeBag[i].tSnare;
           f = friendMatrix[j];
           valj = edgeBag[i].jth;
           vali = edgeBag[i].ith;

           if  (Vnodes[valj] & (1 << j) ) {
              edgeBag[i].zebra2[ticks2] = f;
              centTotal2 = centTotal2 | f;
              ticks2 = ticks2 + 1;
              if ( (( t & f)  == f) ) {
                 Cl = Cl || 1; 
              }
           }
         }

         edgeBag[i].combinedMask2 = centTotal2;
         edgeBag[i].count2 = ticks2;

         if(Ck == 1 || Cl == 1) {
             C2 = C2 && 1;
         }
         else {
             C2 = C2 && 0;
         }

        for (k = 0; k < N; k++) {
	    if( k != edgeBag[i].jth) { 
               for (l = 0; l <= ticks; l++) { // Dynamic
		if (((Tnodes[k]) & edgeBag[i].zebra[l]) != edgeBag[i].zebra[l]) {
	              C3 = C3 && 1;
		 }
	        else {
	              C3 = 0;
		 }
            }
        }  
 }
             
        
        for ( k = 0; k < len; k++) {
           if ( (edgeBag[k] != edgeBag[i])  || (edgeBag[k].jth != edgeBag[i].jth)) { 
               for (l = 0; l <= ticks2; l++) { // Dynamic
	             if (( edgeBag[k].tSnare & edgeBag[i].zebra2[l]) != edgeBag[i].zebra2[l]) 
                          C3 = C3 && 1;
                else 
                      C3 = 0;
                }
       	} 

     }
}
    
/*
    
//  BASIC BLOCK ENDS -----------------------------------------------------------------------------------------
   
    for  (i = 0; i < len; i++) {

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]" , i , edgeBag[i].ith, edgeBag[i].jth);

        printf (" vSnare =  %d \n tSnare = %d\n combinedMask = %d \n counts = %d " ,edgeBag[i].vSnare , edgeBag[i].tSnare, edgeBag[i].combinedMask, edgeBag[i].count);
   
   }

    for  (i = 0; i < N; i++){
        printf("T-Nodes[%d] = %d" , i , Tnodes[i]);
    }
    for  (i = 0; i < N; i++){
        printf("V-Nodes[%d] = %d" , i , Vnodes[i]);
    }
    for  (i = 0; i < snareLength; i++) {
        printf( "\n The frindmatrix[%d] = %d ", i , friendMatrix[i]);
    }

/*
    for  (i = 0; i < N; i++){
        printf(" \n The onOffMatrix[%d] = %d ", i, onOffMatrix[i]);
    }
*/

    for(i = 0;i < N ; i++) {
        for( j = 0;j < N; j++) {
            printf("Graph[%d][%d] = %d",i,j,graph[i][j]);
        }
    }

    printf("\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d \n,C4 : %d , C5 : %d",C0,C1,C2,C3,C4,C5);
    printf(" the value of mr.Ticks is %d and len was %d ", ticks , len);
    
  __CPROVER_assert(! ( C0 && C1 && C2 && C3) , "Graph that satisfy friendZoned model exists");  
 
}

