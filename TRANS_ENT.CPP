/******************************************************************************/
/*                                                                            */
/*  TRANS_ENT - Schreiber's transfer entropy (information transfer)           */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

/*
--------------------------------------------------------------------------------

   We are given two series, x and y, each having n cases.
   It is assumed that p(y[i]) is a function of y[i-1], y[i-2], ..., y[i-yhist].
   But does x[i-xlag], x[i-xlag-1], ..., x[i-xlag-xhist+1] influence the y transition
   probabilities?  This function measures the extent to which this occurs.

   The traditional version has xlag=1, meaning that the value of x concurrent
   with y is not allowed to participate in influencing y.
   Many models want the historical x influence to come up to y,
   allowing concurrent influence.  For this, xlag=0.
   This happens, for example, in developing model-based market trading systems
   in which the indicator/target data is such that indicators are computed
   based strictly on the past and targets strictly on the future.
   So the data already has X inherently lagged to Y, and you would not want
   to lag it still further.

   Note that we have nbins_x ^ xhist * nbins_y ^ (yhist+1) bins.
   In order to get decent probability  estimates, these bins must contain
   a decent number of cases.  The number of bins will blow up fast as
   xhist and yhist grow!  Keep them small unless n is gigantic.

   Suppose 'a' represents the current y, 'b' represents y history, and
   'c' represents x history.  Then the information transfer is:

   SUM [ p(a,b,c) log ( p(a|b,c) / p(a|b) ]

   So it's a sum of logs, weighted by the probability of each possible outcome.
   The log term is the ratio of the conditional probability of the current y
   given both its history and x history, over the conditional given just
   its own (y) history.  If c, the x history, has no impact, this ratio will
   be 1, and its log will be zero.

   Note that p(a|b,c) = p(a,b,c) / p(b,c) and p(a|b) = p(a,b) / p(b)

   To speed calculations, after cumulating p(a,b,c) we compute and save
   the marginals p(b,c), p(a,b), and p(b).

   Four work vectors must be supplied.
   Let nx = nbins_x ^ xhist  and  ny = nbins_y ^ yhist.  The lengths are:
      counts = nx * ny * nbins_y
      ab = nbins_y * ny
      bc = nx * ny
      b = ny

--------------------------------------------------------------------------------
*/

double trans_ent (
   int n ,          // Length of x and y
   int nbins_x ,    // Number of x bins.  Beware if greater than 2.
   int nbins_y ,    // Ditto y
   short int *x ,   // Independent variable, which impacts y transitions
   short int *y ,   // Dependent variable
   int xlag ,       // Lag of most recent predictive x: 1 for traditional, 0 for concurrent
   int xhist ,      // Length of x history.  At least 1; Beware if greater than 1.
   int yhist ,      // Ditto y
   int *counts ,    // Work vector (see comment above)
   double *ab ,     // Ditto
   double *bc ,     // Ditto
   double *b        // Ditto
   )
{
   int i, j, nx, ny, nxy, istart, ix, iy, ia, total ;
   double p, trans, numer, denom ;

/*
   Compute key constants.
*/

   nx = nbins_x ;
   for (i=1 ; i<xhist ; i++)   // Number of bins for X history
      nx *= nbins_x ;

   ny = nbins_y ;
   for (i=1 ; i<yhist ; i++)   // Number of bins for Y history
      ny *= nbins_y ;

   nxy = nx * ny ;             // Total number of history bins

/*
   Pass through the data, cumulating the bin counts
   The counts will be kept in an array with X history changing fastest,
   then Y history, and current Y changing last.
*/

   memset ( counts , 0 , nxy * nbins_y * sizeof(int) ) ;

   istart = xhist + xlag - 1 ;
   if (yhist > istart)
      istart = yhist ;

   for (i=istart ; i<n ; i++) {

      // Which of the nbins_x ^ xhist X history bins does this case lie in?
      ix = x[i-xlag] ;
      for (j=1 ; j<xhist ; j++)
         ix = nbins_x * ix + x[i-j-xlag] ;

      // Which of the nbins_y ^ yhist Y history bins does this case lie in?
      iy = y[i-1] ;
      for (j=2 ; j<=yhist ; j++)
         iy = nbins_y * iy + y[i-j] ;

      ++counts [ y[i] * nxy + iy * nx + ix ] ;  // Increment the correct bin
      }

   total = n - istart ;


/*
   Compute and save the marginals
*/

   for (i=0 ; i<nbins_y*ny ; i++)
      ab[i] = 0.0 ;
   for (i=0 ; i<nx*ny ; i++)
      bc[i] = 0.0 ;
   for (i=0 ; i<ny ; i++)
      b[i] = 0.0 ;

   for (ia=0 ; ia<nbins_y ; ia++) {
      for (iy=0 ; iy<ny ; iy++) {
         for (ix=0 ; ix<nx ; ix++) {
            p = (double) counts [ ia * nxy + iy * nx + ix ] / (double) total ;
            ab[ia*ny+iy] += p ;
            bc[iy*nx+ix] += p ;
            b[iy] += p ;
            }
         }
      }


/*
   Compute the information transfer
*/

   trans = 0.0 ;
   for (ia=0 ; ia<nbins_y ; ia++) {
      for (iy=0 ; iy<ny ; iy++) {
         for (ix=0 ; ix<nx ; ix++) {
            p = (double) counts [ ia * nxy + iy * nx + ix ] / (double) total ;
            if (p <= 0.0)
               continue ;
            numer = p / bc[iy*nx+ix] ;
            denom = ab[ia*ny+iy] / b[iy] ;
            trans += p * log ( numer / denom ) ;
            }
         }
      }

   return trans ;
}
