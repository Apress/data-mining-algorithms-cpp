/******************************************************************************/
/*                                                                            */
/*  PARZDENS - ParzDens_? used for mutual information continuous method       */
/*                                                                            */
/*  These routines transform the raw input data to a normal distribution,     */
/*  so these density estimators are NOT suitable for general use.             */
/*  They are for use by integration routines for computing mutual information.*/
/*  For general use, remove the normal transformation and compute scale       */
/*  factors appropriately.                                                    */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

#if ! defined ( PI )
#define PI 3.141592653589793
#endif

extern double inverse_normal_cdf ( double p ) ;
extern void qsortdsi ( int first , int last , double *data , int *slave ) ;

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

/*
--------------------------------------------------------------------------------

   ParzenDensities ParzDens_? used for continuous mutual information

--------------------------------------------------------------------------------
*/

class ParzDens_1 {

public:
   ParzDens_1 ( int n_tset , double *tset , int n_div ) ;
   ~ParzDens_1 () ;
   double density ( double x ) ;
   double low ;     // Lowest value with significant density
   double high ;    // And highest

private:
   int nd ;         // Number of points in array below
   double *d ;      // The data on which the density is based
   double var ;     // Presumed variance
   double factor ;  // Normalizing factor to make it a density
   CubicSpline *spline ; // Used only if interpolation
} ;

class ParzDens_2 {

public:
   ParzDens_2 ( int n_tset , double *tset0 , double *tset1 , int n_div ) ;
   ~ParzDens_2 () ;
   double density ( double x0 , double x1 ) ;

private:
   int nd ;         // Number of points in arrays below
   double *d0 ;     // The data on which the density is based; first variable
   double *d1 ;     // And second
   double var0 ;    // Presumed variance of first variable
   double var1 ;    // And second
   double factor ;  // Normalizing factor to make it a density
   Bilinear *bilin ; // Used only for bilinear interpolation
} ;

class ParzDens_3 {

public:
   ParzDens_3 ( int n_tset , double *tset0 , double *tset1 , double *tset2 , int n_div ) ;
   ~ParzDens_3 () ;
   double density ( double x0 , double x1 , double x2 ) ;

private:
   int nd ;         // Number of points in arrays below
   double *d0 ;     // The data on which the density is based; first variable
   double *d1 ;     // And second
   double *d2 ;     // And third
   double var0 ;    // Presumed variance of first variable
   double var1 ;    // And second
   double var2 ;    // And third
   double factor ;  // Normalizing factor to make it a density
} ;

/*
--------------------------------------------------------------------------------

   MutualInformation

--------------------------------------------------------------------------------
*/

class MutualInformationParzen {  // Parzen window method

public:
   MutualInformationParzen ( int nn , double *dep_vals , int ndiv ) ;
   ~MutualInformationParzen () ;
   double mut_inf ( double *x ) ;

private:
   int n ;             // Number of cases
   int n_div ;         // Number of divisions of range, typically 5-10
   double *depvals ;   // 'Dependent' variable
   ParzDens_1 *dens_dep ;   // Marginal density of 'dependent' variable
} ;

class MutualInformationAdaptive {  // Adaptive partitioning method

public:
   MutualInformationAdaptive ( int nn , double *dep_vals ,
                               int respect_ties , double crit ) ;
   ~MutualInformationAdaptive () ;
   double mut_inf ( double *x , int respect_ties ) ;

private:
   int n ;             // Number of cases
   int *y ;            // 'Dependent' variable ranks
   int *y_tied ;       // tied[i] != 0 if case with rank i == case with rank i+1
   double chi_crit ;   // Chi-square test criterion
} ;


/*
--------------------------------------------------------------------------------

   ParzDens_1 - Parzen density of a single variable

--------------------------------------------------------------------------------
*/

ParzDens_1::ParzDens_1 ( int n_tset , double *tset , int n_div )
{
   int i, j, *indices ;
   double std, *x, *y, xbot, xinc, diff, sum ;

   nd = n_tset ;
   spline = NULL ;

   d = (double *) malloc ( nd * sizeof(double) ) ;

   indices = (int *) malloc ( nd * sizeof(int) ) ;

/*
   Convert the data to a normal distribution
*/

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d[i] = tset[i] ;
      }
   qsortdsi ( 0 , nd-1 , d , indices ) ;
   for (i=0 ; i<nd ; i++)
      d[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;
   free ( indices ) ;

   std = 2.0 / n_div ;
   var = std * std ;
   high = 3.0 + 3.0 * std ;
   low = -high ;

   factor = 1.0 / (nd * sqrt (2.0 * PI * var) ) ;

   if (nd <= 100)
      return ;

   // We have a lot of cases, so prepare for cubic spline interpolation
   x = (double *) malloc ( 1001 * sizeof(double) ) ;
   y = (double *) malloc ( 1001 * sizeof(double) ) ;

   xinc = (-1.5 - low) / 100.0 ;

   for (i=0 ; i<100 ; i++)
      x[i] = low + i * xinc ;

   xbot = x[99] ;
   xinc = (1.5 - xbot) / 801.0 ;
   for (i=0 ; i<800 ; i++)
      x[i+100] = xbot + (i+1) * xinc ;

   xbot = x[899] ;
   xinc = (high - xbot) / 101.0 ;
   for (i=0 ; i<101 ; i++)
      x[i+900] = xbot + (i+1) * xinc ;

   for (i=0 ; i<1001 ; i++) {
      sum = 0.0 ;
      for (j=0 ; j<nd ; j++) {
         diff = x[i] - d[j] ;
         sum += exp ( -0.5 * diff * diff / var ) ;
         }
      y[i] = factor * sum ;
      }

   spline = new CubicSpline ( 1001 , x , y ) ;

   free ( x ) ;
   free ( y ) ;
}

ParzDens_1::~ParzDens_1 ()
{
   if (d != NULL)
      free ( d ) ;
   if (spline != NULL)
      delete spline ;
}

double ParzDens_1::density ( double x )
{
   int i ;
   double sum, diff ;

   if (spline != NULL)
      return spline->evaluate ( x ) ;

   sum = 0.0 ;
   for (i=0 ; i<nd ; i++) {
      diff = x - d[i];
      sum += exp ( -0.5 * diff * diff / var ) ;
      }

   return sum * factor ;
}

/*
--------------------------------------------------------------------------------

   ParzDens_2 - Parzen density of a bivariate pair

--------------------------------------------------------------------------------
*/

#define P2RES 200

ParzDens_2::ParzDens_2 ( int n_tset , double *tset0 , double *tset1 , int n_div )
{
   int i, j, k, k0, k1, k2, *indices ;
   double *x, *y, *z, xbot, xinc, ybot, yinc, xlow, xhigh, ylow, yhigh, std ;
   double diff0, diff1, sum ;

   nd = n_tset ;

   bilin = NULL ;
   d0 = (double *) malloc ( 2 * nd * sizeof(double) ) ;
   indices = (int *) malloc ( nd * sizeof(int) ) ;
   d1 = d0 + nd ;


/*
   Convert the data to a normal distribution
*/

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d0[i] = tset0[i] ;
      }
   qsortdsi ( 0 , nd-1 , d0 , indices ) ;
   for (i=0 ; i<nd ; i++)
      d0[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d1[i] = tset1[i] ;
      }
   qsortdsi ( 0 , nd-1 , d1 , indices ) ;
   for (i=0 ; i<nd ; i++)
      d1[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;

   free ( indices ) ;

   std = 2.0 / n_div ;
   var0 = var1 = std * std ;
   xhigh = yhigh = 3.0 + 2.0 * std ;
   xlow = ylow = -xhigh ;

   factor = 1.0 / (nd * 2.0 * PI * sqrt ( var0 * var1 ) ) ;

   if (nd <= 100)
      return ;

   // We have a lot of cases, so prepare for bilinear interpolation
   x = (double *) malloc ( P2RES * sizeof(double) ) ;
   y = (double *) malloc ( P2RES * sizeof(double) ) ;
   z = (double *) malloc ( P2RES * P2RES * sizeof(double) ) ;

   if (x == NULL  ||  y == NULL  ||  z == NULL) {
      if (x != NULL)
         free ( x ) ;
      if (y != NULL)
         free ( y ) ;
      if (z != NULL)
         free ( z ) ;
      return ;  // If insufficient memory, do not interpolate
      }

   k0 = (int) (0.1 * P2RES) ;
   xinc = (-1.5 - xlow) / k0 ;
   for (i=0 ; i<k0 ; i++)
      x[i] = xlow + i * xinc ;

   k1 = (int) (0.8 * P2RES) ;
   xbot = x[k0-1] ;
   xinc = (1.5 - xbot) / (k1 + 1) ;
   for (i=0 ; i<k1 ; i++)
      x[i+k0] = xbot + (i+1) * xinc ;

   xbot = x[k0+k1-1] ;
   k2 = P2RES - k0 - k1 ;
   xinc = (xhigh - xbot) / k2 ;
   for (i=0 ; i<k2 ; i++)
      x[i+k0+k1] = xbot + (i+1) * xinc ;


   k0 = (int) (0.1 * P2RES) ;
   yinc = (-1.5 - ylow) / k0 ;
   for (i=0 ; i<k0 ; i++)
      y[i] = ylow + i * yinc ;

   k1 = (int) (0.8 * P2RES) ;
   ybot = y[k0-1] ;
   yinc = (1.5 - ybot) / (k1 + 1) ;
   for (i=0 ; i<k1 ; i++)
      y[i+k0] = ybot + (i+1) * yinc ;

   ybot = y[k0+k1-1] ;
   k2 = P2RES - k0 - k1 ;
   yinc = (yhigh - ybot) / k2 ;
   for (i=0 ; i<k2 ; i++)
      y[i+k0+k1] = ybot + (i+1) * yinc ;

   for (i=0 ; i<P2RES ; i++) {
      for (j=0 ; j<P2RES ; j++) {
         sum = 0.0 ;
         for (k=0 ; k<nd ; k++) {
            diff0 = x[i] - d0[k] ;
            diff1 = y[j] - d1[k] ;
            sum += exp ( -0.5 * (diff0 * diff0 / var0 + diff1 * diff1 / var1 ));
            }
         z[i*P2RES+j] = factor * sum ;
         }
      }

   bilin = new Bilinear ( P2RES , x , P2RES , y , z , 1 ) ;

   free ( x ) ;
   free ( y ) ;
   free ( z ) ;
}

ParzDens_2::~ParzDens_2 ()
{
   if (d0 != NULL)
      free ( d0 ) ;
   if (bilin != NULL)
      delete bilin ;
}

double ParzDens_2::density ( double x0 , double x1 )
{
   int i ;
   double sum, diff0, diff1 ;

   if (bilin != NULL)
      return bilin->evaluate ( x0 , x1 ) ;

   sum = 0.0 ;
   for (i=0 ; i<nd ; i++) {
      diff0 = x0 - d0[i] ;
      diff1 = x1 - d1[i] ;
      sum += exp ( -0.5 * (diff0 * diff0 / var0 + diff1 * diff1 / var1 ) ) ;
      }

   return sum * factor ;
}

/*
--------------------------------------------------------------------------------

   ParzDens_3 - Parzen density of a trivariate trio

--------------------------------------------------------------------------------
*/

ParzDens_3::ParzDens_3 ( int n_tset , double *tset0 , double *tset1 , double *tset2 , int n_div )
{
   int i, *indices ;
   double std ;

   nd = n_tset ;

   d0 = (double *) malloc ( 3 * nd * sizeof(double) ) ;
   indices = (int *) malloc ( nd * sizeof(int) ) ;
   d1 = d0 + nd ;
   d2 = d1 + nd ;

/*
   Convert the data to a normal distribution
*/

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d0[i] = tset0[i] ;
      }
   qsortdsi ( 0 , nd-1 , d0 , indices ) ;
   for (i=0 ; i<nd ; i++)
      d0[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d1[i] = tset1[i] ;
      }
   qsortdsi ( 0 , nd-1 , d1 , indices ) ;
   for (i=0 ; i<nd ; i++)
      d1[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;

   for (i=0 ; i<nd ; i++) {
      indices[i] = i ;
      d2[i] = tset2[i] ;
      }
   qsortdsi ( 0 , nd-1 , d2 , indices ) ;
   for (i=0 ; i<nd ; i++)
      d2[indices[i]] = inverse_normal_cdf ( (i + 1.0) / (nd + 1) ) ;

   free ( indices ) ;

   std = 2.0 / n_div ;
   var0 = var1 = var2 = std * std ;

   factor = 1.0 / (nd * 2.0 * PI * sqrt(2.0 * PI) * sqrt(var0 * var1 * var2) ) ;
}

ParzDens_3::~ParzDens_3 ()
{
   if (d0 != NULL)
      free ( d0 ) ;
}

double ParzDens_3::density ( double x0 , double x1 , double x2 )
{
   int i ;
   double sum, diff0, diff1, diff2 ;

   sum = 0.0 ;
   for (i=0 ; i<nd ; i++) {
      diff0 = x0 - d0[i] ;
      diff1 = x1 - d1[i] ;
      diff2 = x2 - d2[i] ;
      sum += exp ( -0.5 * (diff0 * diff0 / var0 + diff1 * diff1 / var1 +
                           diff2 * diff2 / var2 ) ) ;
      }

   return sum * factor ;
}

