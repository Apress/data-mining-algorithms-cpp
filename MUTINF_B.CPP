/******************************************************************************/
/*                                                                            */
/*  MutInf_B - Mutual information for binary data                             */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

double mutinf_b (
   int n ,         // Number of cases
   short int *y ,  // The 'dependent' variable
   short int *x ,  // The 'independent' variable; NULL to compute H(Y)
   short int *z )  // NULL to compute I(X;Y), z to compute I(X;Y|Z)
{
   int i, nx0, nx1, ny0, ny1, nz0, nz1, n00, n01, n10, n11 ;
   int  n000, n010, n100, n110, n001, n011, n101, n111 ;
   double p, HX, HY, HZ, HXY, HYZ, HXZ, HXYZ ;

/*
--------------------------------------------------------------------------------

   Compute the entropy of Y

--------------------------------------------------------------------------------
*/

   if (x == NULL) {
      ny1 = 0 ;
      for (i=0 ; i<n ; i++) {
         if (y[i])
            ++ny1 ;
         }
      ny0 = n - ny1 ;
      // Compute the entropy of Y
      if (ny0) {
         p = (double) ny0 / (double) n ;
         HY = p * log ( p ) ;
         }
      else
         HY = 0.0 ;
      if (ny1) {
         p = (double) ny1 / (double) n ;
         HY += p * log ( p ) ;
         }
      return -HY ;
      }
/*
--------------------------------------------------------------------------------

   Compute the joint entropy I(X;Y)

--------------------------------------------------------------------------------
*/

   if (z == NULL) {
      n01 = n10 = n11 = 0 ;
      for (i=0 ; i<n ; i++) {
         if (x[i]) {
            if (y[i])
               ++n11 ;
            else
               ++n10 ;
            }
         else {
            if (y[i])
               ++n01 ;
            }
         }
      n00 = n - n01 - n10 - n11 ;
      // Compute the marginals
      nx0 = n00 + n01 ;
      nx1 = n10 + n11 ;
      ny0 = n00 + n10 ;
      ny1 = n01 + n11 ;
      // Compute the entropy of X
      if (nx0) {
         p = (double) nx0 / (double) n ;
         HX = p * log ( p ) ;
         }
      else
         HX = 0.0 ;
      if (nx1) {
         p = (double) nx1 / (double) n ;
         HX += p * log ( p ) ;
         }

      // Compute the entropy of Y
      if (ny0) {
         p = (double) ny0 / (double) n ;
         HY = p * log ( p ) ;
         }
      else
         HY = 0.0 ;
      if (ny1) {
         p = (double) ny1 / (double) n ;
         HY += p * log ( p ) ;
         }

      // Compute the joint entropy H(X,Y)
      if (n00) {
         p = (double) n00 / (double) n ;
         HXY = p * log ( p ) ;
         }
      else
         HXY = 0.0 ;
      if (n01) {
         p = (double) n01 / (double) n ;
         HXY += p * log ( p ) ;
         }
      if (n10) {
         p = (double) n10 / (double) n ;
         HXY += p * log ( p ) ;
         }
      if (n11) {
         p = (double) n11 / (double) n ;
         HXY += p * log ( p ) ;
         }

      return HXY - HX - HY ;
      } // If z==NULL... want I(X;Y)

/*
--------------------------------------------------------------------------------

   Compute the joint conditional entropy I(X;Y|Z)

--------------------------------------------------------------------------------
*/

   else {
      n000 = n001 = n010 = n011 = n100 = n101 = n110 = n111 = 0 ;
      for (i=0 ; i<n ; i++) {
         if (x[i]) {
            if (y[i]) {
               if (z[i])
                  ++n111 ;
               else
                  ++n110 ;
               }
            else {
               if (z[i])
                  ++n101 ;
               else
                  ++n100 ;
               }
            }
         else {
            if (y[i]) {
               if (z[i])
                  ++n011 ;
               else
                  ++n010 ;
               }
            else {
               if (z[i])
                  ++n001 ;
               else
                  ++n000 ;
               }
            }
         }
      // Compute the entropy of Z
      nz0 = n000 + n010 + n100 + n110 ;
      nz1 = n - nz0 ;
      if (nz0) {
         p = (double) nz0 / (double) n ;
         HZ = p * log ( p ) ;
         }
      else
         HZ = 0.0 ;
      if (nz1) {
         p = (double) nz1 / (double) n ;
         HZ += p * log ( p ) ;
         }

      // Compute the joint entropy H(X,Z)
      n00 = n000 + n010 ;
      n01 = n001 + n011 ;
      n10 = n100 + n110 ;
      n11 = n101 + n111 ;
      if (n00) {
         p = (double) n00 / (double) n ;
         HXZ = p * log ( p ) ;
         }
      else
         HXZ = 0.0 ;
      if (n01) {
         p = (double) n01 / (double) n ;
         HXZ += p * log ( p ) ;
         }
      if (n10) {
         p = (double) n10 / (double) n ;
         HXZ += p * log ( p ) ;
         }
      if (n11) {
         p = (double) n11 / (double) n ;
         HXZ += p * log ( p ) ;
         }

      // Compute the joint entropy H(Y,Z)
      n00 = n000 + n100 ;
      n01 = n001 + n101 ;
      n10 = n010 + n110 ;
      n11 = n011 + n111 ;
      if (n00) {
         p = (double) n00 / (double) n ;
         HYZ = p * log ( p ) ;
         }
      else
         HYZ = 0.0 ;
      if (n01) {
         p = (double) n01 / (double) n ;
         HYZ += p * log ( p ) ;
         }
      if (n10) {
         p = (double) n10 / (double) n ;
         HYZ += p * log ( p ) ;
         }
      if (n11) {
         p = (double) n11 / (double) n ;
         HYZ += p * log ( p ) ;
         }

   // Compute the joint entropy H(X,Y,Z)
      if (n000) {
         p = (double) n000 / (double) n ;
         HXYZ = p * log ( p ) ;
         }
      else
         HXYZ = 0.0 ;
      if (n001) {
         p = (double) n001 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n010) {
         p = (double) n010 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n011) {
         p = (double) n011 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n100) {
         p = (double) n100 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n101) {
         p = (double) n101 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n110) {
         p = (double) n110 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      if (n111) {
         p = (double) n111 / (double) n ;
         HXYZ += p * log ( p ) ;
         }
      }

   return HZ + HXYZ - HXZ - HYZ ;
}
