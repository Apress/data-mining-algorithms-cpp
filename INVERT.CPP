//----------------------------------------------------------------------------
/*                           LUDECOMP                                       */
/*                                                                          */
/*   Compute the LU decomposition via Crout algorithm                       */

#include <math.h>
#include <string.h>

int LUdecomp (
   int n ,           // Order of the input matrix
   double *mat_in ,  // Input matrix in standard (row major) order
   double *mat_out , // Output of LU decomposition
   int dim ,         // Their column dimension in the calling routine
   int digits ,      // If > 0 mat_in is assumed to be accurate to digits figs
   double *det ,     // Determinant
   int *pivot ,      // Output of permutation used for pivot optimization
   double *equil )   // Output of smallest 1 / abs (mat_in[i]) for each 

/* It returns 1 if accuracy has not been maintained, 2 if singular. */

{
   int row, col, inner, i, rmax ;
   double sum, fptemp, rn, wrel, big, biggest, *ptr1, *ptr2, *lurc ;
   double ai, wi, wa, p, q, test ;

   rmax = 0 ;  // Not needed.  Shuts up LINT.

/*
   Initialize.  Copy input matrix to output.
*/

   rn = (double) n ;
   wrel = 0.0 ;
   biggest = 0.0 ;
   *det = 1.0 ;

   for (row=0 ; row<n ; row++) {
      big = 0.0 ;
      ptr1 = mat_in + row * dim ;
      ptr2 = mat_out + row * dim ;
      i = n ;
      while (i--) {
         fptemp = *ptr2++ = *ptr1++ ;
         if ((fptemp = fabs ( fptemp )) > big)
            big = fptemp ;
         }
      if (big < 1.0e-90)
         goto SINGULAR ;
      if (big > biggest)
         biggest = big ;
      equil[row] = 1.0 / big ;
      }

/*
-------------------------------------------------------------------------------

   This is the main loop which does all columns

-------------------------------------------------------------------------------
*/

   for (col=0 ; col<n ; col++) {

/*
  First compute all rows of U for this column which are strictly above diagonal.
  Pointer lurc is the current mat_out location.
*/

      for (row=0, lurc=mat_out+col ; row<col ; row++, lurc = lurc + dim) {
         sum = *lurc ;

         if (digits) {  /* Accuracy test */
            ai = fabs ( sum ) ;
            wi = 0.0 ;
            if (row) {
               ptr1 = mat_out + row * dim ;
               ptr2 = mat_out + col ;
               inner = row ;
               while (inner--) {
                  fptemp = *ptr1++  *  *ptr2 ;
                  ptr2 = ptr2 + dim ;
                  sum -= fptemp ;
                  wi += fabs ( fptemp ) ;
                  }
               *lurc = sum ;
               }
            wi += fabs ( sum ) ;
            if (ai < 1.e-90)
               ai = biggest ;
            test = wi / ai ;
            if (test > wrel)
               wrel = test ;
            }  /* if digits (accuracy test) */

         else {   /* No accuracy test */
            if (row) {
               ptr1 = mat_out + row * dim ;
               ptr2 = mat_out + col ;
               inner = row ;
               while (inner--) {
                  sum -= *ptr1++  *  *ptr2 ;
                  ptr2 += dim ;
                  }
               *lurc = sum ;
               }
            } /* No accuracy test */
         }  /* for row */

/*
   Now compute the diagonal of U and the elements of L below the diagonal
*/

      p = 0.0 ;

      for (row=col ; row<n ; row++, lurc = lurc + dim) {  /* lurc still OK */
         sum = *lurc ;
         if (digits) { /* Accuracy test */
            ai = fabs ( sum ) ;
            wi = 0. ;
            if (col) {
               ptr1 = mat_out + row * dim ;
               ptr2 = mat_out + col ;
               inner = col ;
               while (inner--) {
                  fptemp = *ptr1++  *  *ptr2 ;
                  ptr2 = ptr2 + dim ;
                  sum -= fptemp ;
                  wi += fabs ( fptemp ) ;
                  }
               *lurc = sum ;
               }
            wi += fabs ( sum ) ;
            if (ai < 1.e-90)
               ai = biggest ;
            test = wi / ai ;
            if (test > wrel)
               wrel = test ;
            } /*  if digits (accuracy test) */

          else {   /* No accuracy test */
            if (col) {
               ptr1 = mat_out + row * dim ;
               ptr2 = mat_out + col ;
               inner = col ;
               while (inner--) {
                  sum -= *ptr1++  *  *ptr2 ;
                  ptr2 = ptr2 + dim ;
                  }
               *lurc = sum ;
               }
            }  /* no accuracy test */

         q = equil[row] * fabs ( sum ) ;
         if (q > p) {
            p = q ;
            rmax = row ;
            }
         }  /* for row */

      if ((rn + p) == rn) /* No longer can tell them apart? */
         goto SINGULAR ;

/*
   If this row is not the best pivot, interchange for stability
*/

      if (rmax != col) {
         *det = - *det ;
         ptr1 = mat_out + rmax * dim ;
         ptr2 = mat_out + col * dim ;
         inner = n ;
         while (inner--) {
            fptemp = *ptr1 ;
            *ptr1++ = *ptr2 ;
            *ptr2++ = fptemp ;
            }
         equil[rmax] = equil[col] ;
         }

/*
   Final loop housekeeping.  Divide by pivot.
*/

      pivot[col] = rmax ;
      *det *= (fptemp = mat_out[col * dim + col]) ;
      
      ptr1 = mat_out + (col+1) * dim + col ;
      inner = n - col ;
      while (--inner) {
         *ptr1 /= fptemp ;
         ptr1 += dim ;
         }

      }  /* for col */

/*
   All done.  Do final accuracy test.
*/

   if (digits) {
      p = (double) (3 * n + 3) ;
      wa = p * wrel ;
      if (wa + pow ( 10.0 , (double) -digits ) == wa)
         return 1 ;
      }
   return 0 ;

SINGULAR:
   *det = 0.0 ;
   return 2 ;
}

//----------------------------------------------------------------------------
/*                           ELIM                                           */
/*                                                                          */
/*   Elimination part of equation solution (follows LUdecomp)               */

void elim (
   int n ,        // Order of system
   double *lu ,   // LU output of LUdecomp
   int dim ,      // Column dimension of LU in calling program
   double *rhs ,  // Right hand side of system
   int *pivot,    // Pivot output of LUdecomp
   double *x )    // Solution
{
   int ip, row, col, iw ;
   double sum, *ptr1, *ptr2 ;


   memcpy ( x , rhs , n * sizeof(double) ) ; // Copy right hand side to x

/*
   Solve LY = RHS  for Y
*/

   iw = -1 ;
   for (row=0 ; row<n ; row++) {
      ip = pivot[row] ;
      sum = x[ip] ;
      x[ip] = x[row] ;
      if (iw >= 0) {
         ptr1 = lu + row * dim + iw ;
         ptr2 = x + iw ;
         col = row - iw ;
         while (col--)
            sum -= *ptr1++  *  *ptr2++ ;
         }
      else if (fabs ( sum ) > 1.e-90)
         iw = row ;
      x[row] = sum ;
      }

/*
   Now solve UX = Y for X
*/

   for (row=n-1 ; row>=0 ; row--) {
      sum = x[row] ;
      ptr1 = lu + row * dim + row + 1 ;
      ptr2 = x + row + 1 ;
      col = n - row ;
      while (--col)
         sum -= *ptr1++  *  *ptr2++ ;
      x[row] = sum / lu[row * dim + row] ;
      }
}

//----------------------------------------------------------------------------

int invert (
   int n ,           // Size of matrix
   double *x ,       // Matrix to be inverted, not changed
   double *xinv ,    // Output of its inverse
   double *det ,     // Determinant
   double *rwork ,   // Work vector n*n + 2*n long
   int *iwork )      // Work vector n long
{
   int i, j, ret_val ;
   double *lu, *equil, *soln ;

   lu = rwork ;
   equil = lu + n * n ;
   soln = equil + n ;

   ret_val = LUdecomp ( n , x , lu , n , 0 , det , iwork , equil ) ;

   if (ret_val)
      return 1 ;

   for (i=0 ; i<n ; i++) {  // For each column of inverse
      for (j=0 ; j<n ; j++)
         equil[j] = 0.0 ;
      equil[i] = 1.0 ;
      elim ( n , lu , n , equil , iwork , soln ) ;
      for (j=0 ; j<n ; j++)
         xinv[j*n+i] = soln[j] ;
      }

   return 0 ;
}
