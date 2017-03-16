//igraph_subgraph_edges
//igraph_es_vector
/* -*- mode: C -*-  */
/* 
   IGraph library.
   Copyright (C) 2006-2012  Gabor Csardi <csardi.gabor@gmail.com>
   334 Harvard street, Cambridge, MA 02139 USA
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 
   02110-1301 USA

*/
#include "igraph_layout.h"
#include "igraph_random.h"
#include "igraph_components.h"
#include "igraph_types_internal.h"

#include "igraph_adjlist.h"
#include "igraph_community.h"
#include "igraph_memory.h"
#include "igraph_interface.h"
#include "igraph_iterators.h"
#include "config.h"

#include "igraph_datatype.h"
#include "igraph_attributes.h"
#include "igraph_memory.h"

#include "igraph_error.h"
#include "igraph_random.h"
#include "igraph_qsort.h"

#include "igraph_interrupt_internal.h"

#include "igraph_structural.h"
#include "igraph_constructors.h"
#include "igraph_conversion.h"

#include "igraph_attributes.h"

#include <assert.h>
#include <stdlib.h>
#include <stdarg.h>		/* va_start & co */
#include <math.h>
#include <string.h>   /* memset */
#include <stdio.h>
#include <time.h>
#include <R.h>
/**
 * \function igraph_trussness 
 * \brief Finding the trussness of the edges in a network.
 *
 * The k-truss of a graph is a maximal subgraph in which each edge
 * participates in at least k-2 triangles in the subgraph. 
 * The trussness of an edge is the highest order 
 * of a k-truss containing the edge.
 * 
 * </para><para>
 * This function implements the algorithm presented in Jia Wang
 * , James Cheng "Truss decomposition in massive networks.": An O(m^1.5) Algorithm for Truss
 * Decomposition of Networks. 
 * \param graph The input graph.
 * \param truss Pointer to an initialized vector, the result of the
 *        computation will be stored here. It will be resized as
 *        needed. For each edge it contains the highest order of a
 *        truss containing the edge.
 * \return Error code.
 *
 * Time complexity: O(|E|^1.5), the number of edges.
 */

/*int binsort(igraph_matrix_t *arr,igraph_vector_t * edges,igraph_vector_t* sindex,long int h,long int max)
 {
 long int tmpsize,i,j,ind=0;
 igraph_vector_ptr_t bin;
 igraph_vector_ptr_init(&bin,max+1);
 igraph_vector_t* tmp;
 igraph_real_t ed;
 for(i=0;i<=max;i++)
   {
   igraph_vector_t* temp=igraph_Calloc(1,igraph_vector_t);
   VECTOR(bin)[i]=temp;
   } 

 
 for(i=0;i<=h;i++)
   {
   tmp=VECTOR(bin)[(long int)MATRIX(*arr,i,1)];
   igraph_vector_push_back(tmp,MATRIX(*arr,i,0));
   }

 for(i=0;i<=max;i++)
   {
   
   tmp=VECTOR(bin)[i];
   tmpsize=igraph_vector_size(tmp);
   if(tmpsize>0)
   VECTOR(*sindex)[i]=ind;
   else
   VECTOR(*sindex)[i]=-1;
   for(j=0;j<tmpsize;j++)
     {
      ed=VECTOR(*tmp)[j];
     MATRIX(*arr,ind,0)=ed;
     MATRIX(*arr,ind,1)=i;
     VECTOR(*edges)[(long int)ed]=ind;
     ind++;
     }
   }

 return 0;
 }*/

int dominating_set_partitions(const igraph_t *graph,long int no_of_vertices,igraph_vector_ptr_t *res){
  igraph_vector_t d_set,d_set2,result;
  igraph_vector_t bit_array;
  //igraph_vector_init(&d_set,0);
  IGRAPH_VECTOR_INIT_FINALLY(&d_set, 0);
  igraph_vector_ptr_t partition_vertex;
  //igraph_vector_init(&d_set2,0);
  IGRAPH_VECTOR_INIT_FINALLY(&d_set2, 0);
  igraph_vector_t edges;
  //igraph_vector_init(&edges,0);
  IGRAPH_VECTOR_INIT_FINALLY(&edges, 0); 
  //igraph_vector_init(&bit_array,no_of_vertices); //for deleting edges of argument graph update no-of-edges
  IGRAPH_VECTOR_INIT_FINALLY(&bit_array, no_of_vertices);
  igraph_vector_null(&bit_array);
  igraph_vector_t* tmp,*tmp2;

  igraph_vector_t* abc;

  igraph_matrix_t count; //selecting partition
  
  long int countdset=1;  //number of dominating sets(coz 1 is already taken to denote neighbours of seed)

  for(long int i=0;i<no_of_vertices;i++){
  if(VECTOR(bit_array)[i]==0){   
   IGRAPH_CHECK(igraph_neighbors(graph,&edges,i,IGRAPH_ALL));
   int n=igraph_vector_size(&edges);
    
     
    if(n) 
    {
     IGRAPH_CHECK(igraph_vector_push_back (&d_set,i));
       
     for(long int k=0;k<n;k++)
     {
      if(VECTOR(bit_array)[(long int)VECTOR(edges)[k]]==0){
      VECTOR(bit_array)[(long int)VECTOR(edges)[k]]=1; 
      IGRAPH_CHECK(igraph_vector_push_back (&d_set2,(long int)VECTOR(edges)[k]));
      }
     }
    }//if
    //else
     VECTOR(bit_array)[i]=1;
  }//outerif
 }//dominatingset
  

 long int nsize=igraph_vector_size(&d_set),n;
 //Rprintf("Dominating set size is %ld \n",nsize);
 //Rprintf("Dominating set2 size is %ld \n",igraph_vector_size(&d_set2));
 igraph_vector_ptr_init(res,nsize);
 igraph_vector_ptr_init(&partition_vertex,nsize);


 igraph_matrix_init(&count,nsize,2);
  
 for(long int i=0;i<nsize;i++)
   {
   igraph_vector_t* temp=igraph_Calloc(1,igraph_vector_t);
   igraph_vector_t* temp2=igraph_Calloc(1,igraph_vector_t);
   VECTOR(*res)[i]=temp;
   VECTOR(partition_vertex)[i]=temp2;
   igraph_vector_push_back (temp2,(long int)VECTOR(d_set)[i]);
   MATRIX(count,i,1)=1;
   //Rprintf("For vertex %ld temp is %ld \n",i,*temp);
   } 

  
 
   

   long int degree=0,partitiondegree=0;
 //n is the number of neighbors and nsize is the dominating set size
 //degree keeps track of the number of neighbors of vertex currently in all partitions

  //igraph_vector_init(&result,0);
  IGRAPH_VECTOR_INIT_FINALLY(&result, 0);
  
 for(long int i=0;i<igraph_vector_size(&d_set2);i++)
 {
  IGRAPH_CHECK(igraph_neighbors(graph, &edges,(long int)VECTOR(d_set2)[i], IGRAPH_ALL));
  igraph_vector_sort(&edges);
  for(int p=0;p<igraph_vector_size(&edges);p++)
  // Rprintf("%ld",(long int)VECTOR(edges)[p]);
  //Rprintf("\n");
  n=igraph_vector_size(&edges);degree=0;
  if(n)
    {	
     for(long int k=0;k<nsize;k++)
     {
       abc=VECTOR(partition_vertex)[k];
 
      /*for(int p=0;p<igraph_vector_size(VECTOR(partition_vertex)[k]);p++)
          Rprintf("partition vertex %ld",(long int)VECTOR(*abc)[p]);
        Rprintf("\n");*/
  
     
      igraph_vector_intersect_sorted(&edges,VECTOR(partition_vertex)[k], &result);
      degree=igraph_vector_size(&result);
      //Rprintf("For vertex %ld of dset2 neighbour k %ld has degree %ld \n",(long int)VECTOR(d_set2)[i],k,degree);   
      MATRIX(count,k,0)=degree;
      partitiondegree+=degree;  //to keep track of size of the partition     
     }
    
     
     /*Rprintf("For vertex %ld not in dominating set, degree in partition set is %ld \n",i,degree);
     for(long int k=0;k<nsize;k++){
      Rprintf("degree %ld size %ld",(long int)MATRIX(count,k,0),(long int)MATRIX(count,k,1));
     }*/

     long int max=partitiondegree/nsize,selectedpartition;
     //Rprintf("max degree before %d\n\n",max); 
     partitiondegree=0;

     //long int size= igraph_vector_size(VECTOR(*res)[0]);
     
     if((long int)MATRIX(count,0,0)>=max)
     {
      selectedpartition=0;
      max=(long int)MATRIX(count,0,0);   
     }

     for(long int k=1;k<nsize;k++)     //selecting partition
     {
          if((long int)MATRIX(count,k,0)>=max)
          {
             if((long int)MATRIX(count,k,0)>max)
             {
             selectedpartition=k;
             max=(long int)MATRIX(count,k,0);
             }
             else
             {
              if((long int)MATRIX(count,k,1)<(long int)MATRIX(count,selectedpartition,1))
              {
	      selectedpartition=k;               
              }
             }   
          }         
     }
     
     //Rprintf("max degree %d\n\n",max); 
     //Rprintf("Selectedpartion %d",selectedpartition);
     tmp=VECTOR(*res)[selectedpartition];
     tmp2=VECTOR(partition_vertex)[selectedpartition];
     igraph_vector_push_back (tmp2,(long int)VECTOR(d_set2)[i]);

     for(long int k=0;k<n;k++)
     {
      
      igraph_vector_push_back (tmp2,(long int)VECTOR(edges)[k]);
      igraph_vector_push_back (tmp,(long int)VECTOR(d_set2)[i]);
      igraph_vector_push_back (tmp,(long int)VECTOR(edges)[k]);
     }
     igraph_vector_sort(tmp2);
     MATRIX(count,selectedpartition,1)=igraph_vector_size(tmp2); //change the last argument to Matrix macro to 1
    }//if

     
  //assuming connected graph   
  //Rprintf("for loop exiting iteration\n");
 
 }
 
 igraph_matrix_destroy(&count);
 IGRAPH_FINALLY_CLEAN(1); 
 igraph_vector_destroy(&edges);
 igraph_vector_destroy(&bit_array);
 igraph_vector_destroy(&result);
 igraph_vector_destroy(&d_set);
 igraph_vector_destroy(&d_set2);
 igraph_vector_ptr_free_all(&partition_vertex);
 IGRAPH_FINALLY_CLEAN(6);
}//dominating

 int igraph_trussness(const igraph_t *graph, igraph_vector_ptr_t *truss) {
 igraph_vector_ptr_t res;
 igraph_vector_ptr_init(&res, 0);

 dominating_set_partitions(graph,igraph_vcount(graph),&res);

 long int n=igraph_vector_ptr_size(&res);

// Rprintf("size before %ld \n",n);
 igraph_vector_t* abc,eids;
 igraph_es_t es;

 
 IGRAPH_VECTOR_INIT_FINALLY(&eids, 0);
 //igraph_vector_init(&eids,0);
 igraph_t *newg;
 long int j=0;
 for(long int i=0;i<n;i++){
   
   abc=VECTOR(res)[i]; 

   if(igraph_vector_size(abc)>1){
      newg=igraph_Calloc(1, igraph_t);
      if (newg==0) {
       IGRAPH_ERROR("Cannot create graph", IGRAPH_ENOMEM);
       }
      IGRAPH_FINALLY(igraph_free, newg);
   
   /*   Rprintf("Graph for partitions\n\n");
      for(long int p=0;p<igraph_vector_size(abc);p++)
        Rprintf("%ld ",(long int)VECTOR(*abc)[p]);
      Rprintf("\n");
     */
      igraph_get_eids(graph,&eids,abc,0,FALSE, FALSE);

      igraph_es_vector(&es,&eids);
       IGRAPH_FINALLY(igraph_es_destroy, &es);
      //igraph_create(newg,abc,0,FALSE);

      IGRAPH_CHECK(igraph_subgraph_edges(graph,newg,es,TRUE));
  //    Rprintf("vcount %ld ecount %ld \n",igraph_vcount(newg),igraph_ecount(newg));     
      igraph_simplify(newg,TRUE,TRUE,0);
    //  Rprintf("vcount %ld ecount %ld \n",igraph_vcount(newg),igraph_ecount(newg));     
      igraph_vector_ptr_push_back (truss,newg);
          
      IGRAPH_FINALLY_CLEAN(2);
   }//if
   //else
     // igraph_vector_ptr_remove(truss,i);
 }//for
         //IGRAPH_CHECK(igraph_vector_ptr_resize(&res, j));
        n=igraph_vector_ptr_size(truss);
     //   Rprintf("size before %ld \n",n);
        for(long int i=0;i<n;i++){
        newg=VECTOR(*truss)[i];
       // Rprintf("vcount %ld ecount %ld \n",igraph_vcount(newg),igraph_ecount(newg));            
	}
       
       igraph_vector_destroy(abc);
       igraph_es_destroy(&es);
       igraph_vector_destroy(&eids);
       //igraph_Free(newg);
       IGRAPH_FINALLY_CLEAN(3);
       Rprintf("done");
    return 0;
}
