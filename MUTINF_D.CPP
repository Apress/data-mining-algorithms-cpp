/******************************************************************************/
/*                                                                            */
/*  MutInf_D - Mutual information for discrete data                           */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>


class MutualInformationDiscrete {

public:
   MutualInformationDiscrete ( int nc , short int *bins ) ;
   ~MutualInformationDiscrete () ;
   double entropy () ;
   double mut_inf ( short int *bins ) ;
   double conditional ( short int *bins ) ;
   double conditional_error ( short int *bins ) ;
   double HYe ( short int *bins ) ;
   double hPe ( short int *bins ) ;

private:
   int ncases ;         // Number of cases
   short int *bins_y ;  // They are here
   int nbins_y ;        // Number of bins
   int *marginal_y ;    // Marginal distribution
} ;


/*
--------------------------------------------------------------------------------

   MutualInformationDiscrete - Constructor and destructor

--------------------------------------------------------------------------------
*/


MutualInformationDiscrete::MutualInformationDiscrete (
   int nc ,      // Number of cases
   short int *bins )   // They are here (y, the 'dependent' variable)
{
   int i ;

/*
   Keep a local copy of the bins
*/

   ncases = nc ;

   bins_y = (short int *) malloc ( ncases * sizeof(short int) ) ;

   memcpy ( bins_y , bins , ncases * sizeof(short int) ) ;

/*
   Compute the number of bins, and then compute and save the marginal distribution
*/

   nbins_y = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_y[i] > nbins_y)
         nbins_y = bins_y[i] ;
      }
   ++nbins_y ;  // Number of bins is one greater than max bin because org=0

   marginal_y = (int *) malloc ( nbins_y * sizeof(int) ) ;
   assert (marginal_y != NULL) ;

   for (i=0 ; i<nbins_y ; i++)
      marginal_y[i] = 0 ;

   for (i=0 ; i<ncases ; i++)
      ++marginal_y[bins_y[i]] ;
}

MutualInformationDiscrete::~MutualInformationDiscrete ()
{
   free ( bins_y ) ;
   free ( marginal_y ) ;
}

/*
--------------------------------------------------------------------------------

   entropy() - Compute the entropy of Y, the 'dependent' variable

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::entropy ()
{
   int i ;
   double p, ent ;

   ent = 0.0 ;
   for (i=0 ; i<nbins_y ; i++) {
      if (marginal_y[i] > 0) {
         p = (double) marginal_y[i] / ncases ;
         ent += p * log ( p ) ;
         }
      }
   return -ent ;
}

/*
--------------------------------------------------------------------------------

   conditional ( bins_x ) - Compute the conditional entropy of Y given X

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::conditional ( short int *bins_x )
{
   int i, ix, iy, nbins_x, *grid, *marginal_x ;
   double CI, pyx, cix ;

/*
   Compute the number of bins
*/

   nbins_x = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_x[i] > nbins_x)
         nbins_x = bins_x[i] ;
      }
   ++nbins_x ;  // Number of bins is one greater than max bin because org=0

/*
   Compute the marginal of x and the counts in the nbins_x by nbins_y grid
*/

   marginal_x = (int *) malloc ( nbins_x * sizeof(int) ) ;

   grid = (int *) malloc ( nbins_x * nbins_y * sizeof(int) ) ;

   for (ix=0 ; ix<nbins_x ; ix++) {
      marginal_x[ix] = 0 ;
      for (iy=0 ; iy<nbins_y ; iy++)
         grid[ix*nbins_y+iy] = 0 ;
      }

   for (i=0 ; i<ncases ; i++) {
      ix = bins_x[i] ;
      ++marginal_x[ix] ;
      ++grid[ix*nbins_y+bins_y[i]] ;
      }

/*
   Compute the conditional entropy
*/

   CI = 0.0 ;
   for (ix=0 ; ix<nbins_x ; ix++) {
      if (marginal_x[ix] > 0) {
         cix = 0.0 ;
         for (iy=0 ; iy<nbins_y ; iy++) {
            pyx = (double) grid[ix*nbins_y+iy] / (double) marginal_x[ix] ;
            if (pyx > 0.0)
               cix += pyx * log ( pyx ) ;
            }
         }
      CI += cix * marginal_x[ix] / ncases ;
      }

   free ( marginal_x ) ;
   free ( grid ) ;

   return -CI ;
}

/*
--------------------------------------------------------------------------------

   mut_inf ( bins_x ) - Compute the mutual information I(X;Y)

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::mut_inf ( short int *bins_x )
{
   int i, j, ix, nbins_x, *grid, *marginal_x ;
   double MI, px, py, pxy ;

/*
   Compute the number of bins
*/

   nbins_x = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_x[i] > nbins_x)
         nbins_x = bins_x[i] ;
      }
   ++nbins_x ;  // Number of bins is one greater than max bin because org=0

/*
   Compute the marginal of x and the counts in the nbins_x by nbins_y grid
*/

   marginal_x = (int *) malloc ( nbins_x * sizeof(int) ) ;
   assert (marginal_x != NULL) ;

   grid = (int *) malloc ( nbins_x * nbins_y * sizeof(int) ) ;
   assert ( grid != NULL ) ;

   for (i=0 ; i<nbins_x ; i++) {
      marginal_x[i] = 0 ;
      for (j=0 ; j<nbins_y ; j++)
         grid[i*nbins_y+j] = 0 ;
      }

   for (i=0 ; i<ncases ; i++) {
      ix = bins_x[i] ;
      ++marginal_x[ix] ;
      ++grid[ix*nbins_y+bins_y[i]] ;
      }

/*
   Compute the mutual information
*/

   MI = 0.0 ;
   for (i=0 ; i<nbins_x ; i++) {
      px = (double) marginal_x[i] / (double) ncases ;
      for (j=0 ; j<nbins_y ; j++) {
         py = (double) marginal_y[j] / (double) ncases ;
         pxy = (double) grid[i*nbins_y+j] / (double) ncases ;
         if (pxy > 0.0)
            MI += pxy * log ( pxy / (px * py) ) ;
         }
      }

   free ( marginal_x ) ;
   free ( grid ) ;

   return MI ;
}

/*
--------------------------------------------------------------------------------

   hPe ( bins_x ) - Compute the Shannon entropy of the probability of error
                    This only makes sense if X and Y have the same number of
                    bins, and the bin of X is a prediction of the bin of Y.

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::hPe ( short int *bins_x )
{
   int i, err ;
   double p ;

   err = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_x[i] != bins_y[i])
         ++err ;
      }

   if (err == 0  ||  err == ncases)
      return 0.0 ;

   p = (double) err / (double) ncases ;
   return -p * log ( p ) - (1.0 - p) * log ( 1.0 - p ) ;
}

/*
--------------------------------------------------------------------------------

   conditional_error ( bins_x ) - Compute the conditional error entropy given X

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::conditional_error ( short int *bins_x )
{
   int i, ix, nbins_x, *error_count, *marginal_x ;
   double CI, pyx ;

/*
   Compute the number of bins
*/

   nbins_x = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_x[i] > nbins_x)
         nbins_x = bins_x[i] ;
      }
   ++nbins_x ;  // Number of bins is one greater than max bin because org=0

/*
   Compute the marginal of x and the error counts
*/

   marginal_x = (int *) malloc ( nbins_x * sizeof(int) ) ;
   assert (marginal_x != NULL) ;

   error_count = (int *) malloc ( nbins_x * sizeof(int) ) ;
   assert ( error_count != NULL ) ;

   for (ix=0 ; ix<nbins_x ; ix++) {
      marginal_x[ix] = 0 ;
      error_count[ix] = 0 ;
      }

   for (i=0 ; i<ncases ; i++) {
      ix = bins_x[i] ;
      ++marginal_x[ix] ;
      if (bins_y[i] != ix)
         ++error_count[ix] ;
      }

/*
   Compute the conditional error entropy
*/

   CI = 0.0 ;
   for (ix=0 ; ix<nbins_x ; ix++) {
      if (error_count[ix] > 0  &&  error_count[ix] < marginal_x[ix]) {
         pyx = (double) error_count[ix] / (double) marginal_x[ix] ;
         CI += (pyx * log(pyx) + (1.0-pyx) * log(1.0-pyx)) * marginal_x[ix] / ncases ;
         }
      }

   free ( marginal_x ) ;
   free ( error_count ) ;

   return -CI ;
}

/*
--------------------------------------------------------------------------------

   HYe ( bins_x ) - Compute the minimum (over bins of X) conditional entropy
                    H(Y|error,X).  In other words, for each X bin,compute the
                    conditional entropy of Y given that this X is an incorrect
                    decision.  Return the minimum of this value across X bins.
                    This only makes sense if X and Y have the same number of
                    bins, and the bin of X is a prediction of the bin of Y.

--------------------------------------------------------------------------------
*/

double MutualInformationDiscrete::HYe ( short int *bins_x )
{
   int i, ix, iy, nbins_x, nerr, *grid, *marginal_x ;
   double minCI, pyx, cix ;

/*
   Compute the number of bins
*/

   nbins_x = 0 ;
   for (i=0 ; i<ncases ; i++) {
      if (bins_x[i] > nbins_x)
         nbins_x = bins_x[i] ;
      }
   ++nbins_x ;  // Number of bins is one greater than max bin because org=0

/*
   This algorithm makes sense only if nbins_x equals nbins_y.
   Return an error flag that will get the user's attention if this is violated.
*/

   if (nbins_x != nbins_y)
      return -1.e60 ;

/*
   Compute the marginal of x and the counts in the nbins_x by nbins_y grid
*/

   marginal_x = (int *) malloc ( nbins_x * sizeof(int) ) ;
   assert (marginal_x != NULL) ;

   grid = (int *) malloc ( nbins_x * nbins_y * sizeof(int) ) ;
   assert ( grid != NULL ) ;

   for (ix=0 ; ix<nbins_x ; ix++) {
      marginal_x[ix] = 0 ;
      for (iy=0 ; iy<nbins_y ; iy++)
         grid[ix*nbins_y+iy] = 0 ;
      }

   for (i=0 ; i<ncases ; i++) {
      ix = bins_x[i] ;
      ++marginal_x[ix] ;
      ++grid[ix*nbins_y+bins_y[i]] ;
      }

/*
   Compute the minimum entropy, conditional on error and each X
   Note that the computation in the inner loop is almost the same as in the
   conditional entropy.  The only difference is that since we are also
   conditioning on the classification being in error, we must remove from
   the X marginal the diagonal element, which is the correct decision.
   The outer loop looks for the minimum, rather than summing.
*/

   minCI = 1.e60 ;
   for (ix=0 ; ix<nbins_x ; ix++) {
      nerr = marginal_x[ix] - grid[ix*nbins_y+ix] ; // Marginal that is in error
      if (nerr > 0) {
         cix = 0.0 ;
         for (iy=0 ; iy<nbins_y ; iy++) {
            if (iy == ix)  // This is the correct decision
               continue ;  // So we exclude it; we are summing over errors
            pyx = (double) grid[ix*nbins_y+iy] / (double) nerr ;
            if (pyx > 0.0)
               cix -= pyx * log ( pyx ) ;
            }
         if (cix < minCI)
            minCI = cix ;
         }
      }

   free ( marginal_x ) ;
   free ( grid ) ;

   return minCI ;
}
