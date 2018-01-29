/******************************************************************************/
/*                                                                            */
/*  BILINEAR - Bilinear class for two-dimensional interpolation               */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

class Bilinear {

public:
   Bilinear ( int nxin , double *xin , int nyin , double *yin , double *zin ,
              int extra ) ;
   ~Bilinear () ;
   double evaluate ( double x , double y ) ;

private:
   int quadratic ;
   int nx ;
   int ny ;
   double *x ;
   double *y ;
   double *z ;
} ;


Bilinear::Bilinear ( // Uses input points (x,y,z) where z=f(x,y)
   int nxin ,        // Number of x points
   double *xin ,     // They are here, sorted ascending
   int nyin ,        // Number of y points
   double *yin ,     // They are here, sorted ascending
   double *zin ,     // Corresponding function values, y changing fastest
   int extra         // If nonzero, use 3x3 block with quadratic interpolation
   )
{

   quadratic = extra ;
   nx = nxin ;
   ny = nyin ;
   x = (double *) malloc ( nx * sizeof(double) ) ;
   y = (double *) malloc ( ny * sizeof(double) ) ;
   z = (double *) malloc ( nx * ny * sizeof(double) ) ;
   assert ( x != NULL ) ;
   assert ( y != NULL ) ;
   assert ( z != NULL ) ;

   memcpy ( x , xin , nx * sizeof(double) ) ;
   memcpy ( y , yin , ny * sizeof(double) ) ;
   memcpy ( z , zin , nx * ny * sizeof(double) ) ;
}

Bilinear::~Bilinear ()
{
   free ( x ) ;
   free ( y ) ;
   free ( z ) ;
}

double Bilinear::evaluate ( double xpt , double ypt )
{
   int k, kxlo, kxmid, kxhi, kylo, kymid, kyhi ;
   double t, u, val, clo, cmid, chi, zlo, zmid, zhi ;
   double dlo, dmid, dhi, lo_mid, lo_hi, mid_hi ;

/*
   Bound outlying inputs
*/

   if (xpt < x[0])
      xpt = x[0] ;
   if (xpt > x[nx-1])
      xpt = x[nx-1] ;
   if (ypt < y[0])
      ypt = y[0] ;
   if (ypt > y[ny-1])
      ypt = y[ny-1] ;

/*
   Find the pair of x coordinates that bound the input
*/

   kxlo = 0 ;
   kxhi = nx - 1 ;
   while (kxhi > kxlo+1) {
      k = (kxhi + kxlo) / 2 ;
      if (xpt < x[k])
         kxhi = k ;
      else
         kxlo = k ;
      }

/*
   Find the pair of y coordinates that bound the input
*/

   kylo = 0 ;
   kyhi = ny - 1 ;
   while (kyhi > kylo+1) {
      k = (kyhi + kylo) / 2 ;
      if (ypt < y[k])
         kyhi = k ;
      else
         kylo = k ;
      }

/*
   3x3 with quadratic interpolation?
*/

   if (quadratic) {
      // Choose which way to go for the third x point
      if (kxlo == 0) {
         kxmid = kxhi ;
         ++kxhi ;
         }
      else if (kxhi == nx-1) {
         kxmid = kxlo ;
         --kxlo ;
         }
      else if (xpt-x[kxlo] < x[kxhi]-xpt) {
         kxmid = kxlo ;
         --kxlo ;
         }
      else {
         kxmid = kxhi ;
         ++kxhi ;
         }

      // Choose which way to go for the third y point
      if (kylo == 0) {
         kymid = kyhi ;
         ++kyhi ;
         }
      else if (kyhi == ny-1) {
         kymid = kylo ;
         --kylo ;
         }
      else if (ypt-y[kylo] < y[kyhi]-ypt) {
         kymid = kylo ;
         --kylo ;
         }
      else {
         kymid = kyhi ;
         ++kyhi ;
         }

      dlo = xpt - x[kxlo] ;
      dmid = xpt - x[kxmid] ;
      dhi = xpt - x[kxhi] ;
      lo_mid = x[kxlo] - x[kxmid] ;
      lo_hi = x[kxlo] - x[kxhi] ;
      mid_hi = x[kxmid] - x[kxhi] ;
      clo = dmid * dhi / (lo_mid * lo_hi) ;
      cmid = dlo * dhi / (-lo_mid * mid_hi) ;
      chi = dlo * dmid / (lo_hi * mid_hi) ;

      zlo  = clo * z[kxlo*ny+kylo]  + cmid * z[kxmid*ny+kylo]  + chi * z[kxhi*ny+kylo] ;
      zmid = clo * z[kxlo*ny+kymid] + cmid * z[kxmid*ny+kymid] + chi * z[kxhi*ny+kymid] ;
      zhi  = clo * z[kxlo*ny+kyhi]  + cmid * z[kxmid*ny+kyhi]  + chi * z[kxhi*ny+kyhi] ;

      dlo = ypt - y[kylo] ;
      dmid = ypt - y[kymid] ;
      dhi = ypt - y[kyhi] ;
      lo_mid = y[kylo] - y[kymid] ;
      lo_hi = y[kylo] - y[kyhi] ;
      mid_hi = y[kymid] - y[kyhi] ;
      clo = dmid * dhi / (lo_mid * lo_hi) ;
      cmid = dlo * dhi / (-lo_mid * mid_hi) ;
      chi = dlo * dmid / (lo_hi * mid_hi) ;

      return clo * zlo + cmid * zmid + chi * zhi ;
      } // If quadratic

/*
   Ordinary 2x2 bilinear
*/

   else {
      t = (xpt - x[kxlo]) / (x[kxhi] - x[kxlo]) ;
      u = (ypt - y[kylo]) / (y[kyhi] - y[kylo]) ;

      val = (1.0 - t) * (1.0 - u) * z[kxlo*ny+kylo] ;
      val += t * (1.0 - u) * z[kxhi*ny+kylo] ;
      val += t * u * z[kxhi*ny+kyhi] ;
      val += (1.0 - t) * u * z[kxlo*ny+kyhi] ;
      return val ;
      }
}
