/******************************************************************************/
/*                                                                            */
/*  SPEARMAN - Compute Spearman Rho                                           */
/*                                                                            */
/******************************************************************************/

#include <math.h>
#include <string.h>

extern void qsortds ( int first , int last , double *data , double *slave ) ;

double spearman (  // Returns rho in range -1 to 1
   int n ,         // Input: Number of cases
   double *var1 ,  // Input: One variable
   double *var2 ,  // Input: Other variable
   double *x ,     // Work vector n long
   double *y       // Work vector n long
   )
{
   int j, k, ntied ;
   double val, x_tie_correc, y_tie_correc ;
   double dn, ssx, ssy, rank, diff, rankerr, rho ;

   // We need to rearrange input vectors, so copy them to work vectors
   // To avoid disturbing the caller
   if (x != var1)
      memcpy ( x , var1 , n * sizeof(double) ) ;
   if (y != var2)
      memcpy ( y , var2 , n * sizeof(double) ) ;

   // Compute ties in x, compute correction as SUM ( ties**3 - ties )
   // The following routine sorts x ascending and simultaneously moves y
   qsortds ( 0 , n-1 , x , y ) ;
   x_tie_correc = 0.0 ;
   for (j=0 ; j<n ; ) { // Convert x to ranks, cumulate tie corec
      val = x[j] ;
      for (k=j+1 ; k<n ; k++) {  // Find all ties
         if (x[k] > val)
            break ;
         }
      ntied = k - j ;
      x_tie_correc += (double) ntied * ntied * ntied - ntied ;
      rank = 0.5 * ((double) j + (double) k + 1.0) ;
      while (j < k)
         x[j++] = rank ;
      } // For each case in sorted x array

   // Now do same for y
   qsortds ( 0 , n-1 , y , x ) ;
   y_tie_correc = 0.0 ;
   for (j=0 ; j<n ; ) { // Convert y to ranks, cumulate tie corec
      val = y[j] ;
      for (k=j+1 ; k<n ; k++) {  // Find all ties
         if (y[k] > val)
            break ;
         }
      ntied = k - j ;
      y_tie_correc += (double) ntied * ntied * ntied - ntied ;
      rank = 0.5 * ((double) j + (double) k + 1.0) ;
      while (j < k)
         y[j++] = rank ;
      } // For each case in sorted y array

   // Final computations
   dn = n ;
   ssx = (dn * dn * dn - dn - x_tie_correc) / 12.0 ;
   ssy = (dn * dn * dn - dn - y_tie_correc) / 12.0 ;
   rankerr = 0.0 ;
   for (j=0 ; j<n ; j++) { // Cumulate squared rank differences
      diff = x[j] - y[j] ;
      rankerr += diff * diff ;
      }
   rho = 0.5 * (ssx + ssy - rankerr) / sqrt (ssx * ssy + 1.e-20) ;
   return rho ;
}
