/******************************************************************************/
/*                                                                            */
/*  SPLINE - CubicSpline class                                                */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

extern void qsortds ( int first , int last , double *x , double *y ) ;

class CubicSpline {

public:
   CubicSpline ( int n , double *xin , double *yin ) ;
   ~CubicSpline () ;
   double evaluate ( double x ) ;

private:
   int n ;
   double *x ;
   double *y ;
   double *y2 ;
} ;


CubicSpline::CubicSpline (
   int nin ,       // Number of input points
   double *xin ,   // They are here, not necessarily sorted
   double *yin
   )
{
   int i ;
   double temp, p, *c ;

   n = nin ;
   c =  (double *) malloc ( n * sizeof(double) ) ;
   x =  (double *) malloc ( n * sizeof(double) ) ;
   y =  (double *) malloc ( n * sizeof(double) ) ;
   y2 = (double *) malloc ( n * sizeof(double) ) ;

   assert ( c != NULL ) ;
   assert ( x != NULL ) ;
   assert ( y != NULL ) ;
   assert ( y2 != NULL ) ;

   memcpy ( x , xin , n * sizeof(double) ) ;
   memcpy ( y , yin , n * sizeof(double) ) ;
   qsortds ( 0 , n-1 , x , y ) ;

   y2[0] = c[0] = 0.0 ;

   for (i=1 ; i<n-1 ; i++) {
      temp = (x[i] - x[i-1]) / (x[i+1] - x[i-1]) ;
      p = temp * y2[i-1] + 2.0 ;
      y2[i] = (temp - 1.0) / p ;
      c[i] = (y[i+1] - y[i]) / (x[i+1] - x[i]) ;
      c[i] -= (y[i] - y[i-1]) / (x[i] - x[i-1]) ;
      c[i] = (6.0 * c[i] / (x[i+1] - x[i-1]) - temp * c[i-1]) / p ;
      }

   y2[n-1] = 0.0 ;
   for (i=n-2 ; i>=0 ; i--)
      y2[i] = y2[i] * y2[i+1] + c[i] ;

   free ( c ) ;
}

CubicSpline::~CubicSpline ()
{
   free ( x ) ;
   free ( y ) ;
   free ( y2 ) ;
}

double CubicSpline::evaluate ( double xpt )
{
   int k, klo, khi ;
   double dist, a, b, aa, bb, val ;

   if (xpt < x[0])
      return y[0] ;

   if (xpt > x[n-1])
      return y[n-1] ;

   klo = 0 ;
   khi = n - 1 ;

   while (khi > klo+1) {
      k = (khi + klo) / 2 ;
      if (xpt < x[k])
         khi = k ;
      else
         klo = k ;
      }

   dist = x[khi] - x[klo] + 1.e-60 ;
   a = (x[khi] - xpt) / dist ;
   b = (xpt - x[klo]) / dist ;
   aa = a * (a * a - 1.0) ;
   bb = b * (b * b - 1.0) ;

   val = (aa * y2[klo] + bb * y2[khi]) * dist * dist / 6.0 ;
   return a * y[klo] + b * y[khi] + val ;
}
