/******************************************************************************/
/*                                                                            */
/*  PART - Partition an array into roughly equal size bins, avoiding ties     */
/*                                                                            */
/*  I make no special claims of optimality for this algorithm, largely        */
/*  because there is no single optimality criterion!  All algorithms involve  */
/*  tradeoffs.  However, I am reasonably certain that this algorithm has two  */
/*  valuable properties:                                                      */
/*                                                                            */
/*  1) If the user inputs npart at least as large as the number of distinct   */
/*     values in the dataset, npart will be returned equal to the number of   */
/*     distinct values in the dataset, and each bin will correspond exactly   */
/*     to a distinct value.                                                   */
/*                                                                            */
/*  2) If the data has few or no ties, and the user inputs npart much less    */
/*     than n, the dataset will be partitioned into npart bins, all of which  */
/*     have equal or very nearly equal size.                                  */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

extern void qsortdsi ( int first , int last , double *data , int *slave ) ;

void partition (
   int n ,         // Input: Number of cases in the data array
   double *data ,  // Input: The data array
   int *npart ,    // Input/Output: Number of partitions to find; Returned as
                   // actual number of partitions, which happens if massive ties
   double *bnds ,  // Output: Upper bound (inclusive) of each partition
                   // If the user inputs this NULL, bounds are not returned
   short int *bins // Output: Bin id (0 through npart-1) for each case
   )
{
   int i, j, k, np, *ix, *indices, *bin_end, ibound, tie_found ;
   int istart, istop, nleft, nright, nbest, ibound_best, isplit_best ;
   double *x ;

   if (*npart > n)  // Defend against a careless user
      *npart = n ;

   np = *npart ;    // Will be number of partitions

   x = (double *) malloc ( n * sizeof(double) ) ;
   ix = (int *) malloc ( n * sizeof(int) ) ;
   indices = (int *) malloc ( n * sizeof(int) ) ;
   bin_end = (int *) malloc ( np * sizeof(int) ) ;

/*
   Sort the data and compute an integer rank array that identifies ties.
   We could use the x array, but the code later will run faster if it can
   work with integers instead of reals.
   Also keep the indices of the original data points, as we will need this
   information at the end of this code to assign cases to bins.
*/

   for (i=0 ; i<n ; i++) {
      x[i] = data[i] ;
      indices[i] = i ;
      }

   qsortdsi ( 0 , n-1 , x , indices ) ;

   ix[0] = k = 0 ;
   for (i=1 ; i<n ; i++) {
      if (x[i] - x[i-1] >= 1.e-12 * (1.0 + fabs(x[i]) + fabs(x[i-1])))
         ++k ;     // If not a tie, advance the counter of unique values
      ix[i] = k ;
      }

/*
   Compute initial bounds based strictly on equal number of cases in each bin.
   Ignore ties for now.
*/

   k = 0 ;                              // Will be start of next bin up
   for (i=0 ; i<np ; i++) {             // For all partitions
      j = (n - k) / (np - i) ;          // Number of cases in this partition
      k += j ;                          // Advance the index of next one up
      bin_end[i] = k-1 ;                // Store upper bound of this bin
      }

/*
   If the data has no ties, we are done.  But if there are ties, we must iterate
   until no partition boundary splits a tie.
   Note that the upper bound of the last partition is always the last case
   in the sorted array, so we don't need to worry about it splitting a tie.
   There are no cases above it!  All we care about are the np-1 internal
   boundaries.
*/

   for (;;) {

      tie_found = 0 ;

      for (ibound=0 ; ibound<np-1 ; ibound++) {
         if (ix[bin_end[ibound]] == ix[bin_end[ibound]+1]) { // Splits a tie?
            // This bound splits a tie.  Remove this bound.
            for (i=ibound+1 ; i<np ; i++)
               bin_end[i-1] = bin_end[i] ;
            --np ;
            tie_found = 1 ;
            break ;
            }
         } // For all bounds, looking for a split across a tie

      if (! tie_found)  // If we got all the way through the loop
         break ;        // without finding a bad bound, we are done

      // The offending bound is now gone.  Try splitting each remaining
      // bin.  For each split, check the size of the smaller resulting bin.
      // Choose the split that gives the largest of the smaller.
      // Note that np has been decremented, so now np < *npart.

      istart = 0 ;
      nbest = -1 ;
      for (ibound=0 ; ibound<np ; ibound++) {
         istop = bin_end[ibound] ;
         // Now processing a bin from istart through istop, inclusive
         for (i=istart ; i<istop ; i++) { // Try all possible splits of this bin
            if (ix[i] == ix[i+1])         // If this splits a tie
               continue ;                 // Don't check
            nleft = i - istart + 1 ;      // Number of cases in left half
            nright = istop - i ;          // And right half
            if (nleft < nright) {
               if (nleft > nbest) {
                  nbest = nleft ;
                  ibound_best = ibound ;
                  isplit_best = i ;
                  }
               }
            else {
               if (nright > nbest) {
                  nbest = nright ;
                  ibound_best = ibound ;
                  isplit_best = i ;
                  }
               }
            }
         istart = istop + 1 ;
         } // For all bounds, looking for the best bin to split

      // The search is done.  It may (rarely) be the case that no further
      // splits are possible.  This will happen if the user requests more
      // partitions than there are unique values in the dataset.
      // We know that this has happened if nbest is still -1.  In this case
      // we (obviously) cannot do a split to make up for the one lost above.

      if (nbest < 0)
         continue ;

      // We get here when the best split of an existing partition has been
      // found.  Save it.  The bin that we are splitting is ibound_best,
      // and the split for a new bound is at isplit_best.

      for (ibound=np-1 ; ibound>=ibound_best ; ibound--)
         bin_end[ibound+1] = bin_end[ibound] ;
      bin_end[ibound_best] = isplit_best ;
      ++np ;

      } // Endless search loop

/*
   The partition bounds are found.
   Return them to the user if requested.
*/

   *npart = np ;   // Return the final number of partitions

   if (bnds != NULL) {  // Does the user want the boundary values?
      for (ibound=0 ; ibound<np ; ibound++)
         bnds[ibound] = x[bin_end[ibound]] ;
      }

/*
   Return the bin membership of each case in the dataset
*/

   istart = 0 ;                            // The current bin starts here
   for (ibound=0 ; ibound<np ; ibound++) { // Process all bins
      istop = bin_end[ibound] ;            // Inclusive end of this bin
      for (i=istart ; i<=istop ; i++)
         bins[indices[i]] = (short int) ibound ;
      istart = istop + 1 ;
      }

   free ( x ) ;
   free ( ix ) ;
   free ( indices ) ;
   free ( bin_end ) ;
}
