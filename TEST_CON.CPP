/******************************************************************************/
/*                                                                            */
/*  TEST_CON - Test the continuous mutual information methods                 */
/*                                                                            */
/******************************************************************************/

#include <stdio.h>
#include <string.h>
#include <math.h>
#include <conio.h>
#include <ctype.h>
#include <stdlib.h>

extern double normal () ;
extern double unifrand () ;

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


int main (
   int argc ,    // Number of command line arguments (includes prog name)
   char *argv[]  // Arguments (prog name is argv[0])
   )

{
   int i, nsamps, ntries, ndiv, divisor, itry, respect_ties ;
   double corr, correct, ptie, *x, *y, x1, x2, result, prior_x1 ;
   double total_parzen, bias_parzen, stderr_parzen ;
   double total_adapt, bias_adapt, stderr_adapt ;
   double chi_test ;
   MutualInformationParzen *mi_parzen ;
   MutualInformationAdaptive *mi_adapt ;

/*
   Process command line parameters
*/

#if 1
   if (argc != 8) {
      printf (
         "\nUsage: TEST_CON nsamples ntries correlation ptie respect_ties ndiv chi_test" ) ;
      exit ( 1 ) ;
      }

   nsamps = atoi ( argv[1] ) ;
   ntries = atoi ( argv[2] ) ;
   corr = atof ( argv[3] ) ;
   ptie = atof ( argv[4] ) ;
   respect_ties = atoi ( argv[5] ) ;
   ndiv = atoi ( argv[6] ) ;
   chi_test = atof ( argv[7] ) ;
#else
   nsamps = 101 ;
   ntries = 10 ;
   corr = 0.9 ;
   ptie = 0.0 ;
   respect_ties = 0 ;
   ndiv = 5 ;
   chi_test = 6.0 ;
#endif

   if ((nsamps <= 0)  ||  (ntries <= 0)  || (corr < -1.0)  ||  (corr > 1.0)
    || (ptie < 0.0)  || (ptie > 1.0)  || (ndiv < 2)  || (chi_test < 0.0)) {
      printf (
         "\nUsage: TEST_CON nsamples ntries correlation ptie respect_ties ndiv chi_test" ) ;
      exit ( 1 ) ;
      }


/*
   Allocate memory and initialize
*/

   divisor = ntries / 100 ;  // This is for progress reports only
   if (divisor < 1)
      divisor = 1 ;

   x = (double *) malloc ( nsamps * sizeof(double) ) ;
   y = (double *) malloc ( nsamps * sizeof(double) ) ;


/*
   Main outer loop does all tries
*/

   correct = -0.5 * log ( 1.0 - corr * corr ) ;
   total_parzen = bias_parzen = stderr_parzen = 0.0 ;
   total_adapt = bias_adapt = stderr_adapt = 0.0 ;

   for (itry=1 ; itry<=ntries ; itry++) {

      if (((itry-1) % divisor) == 0)
         printf ( "\n\n\nTry %d of %d", itry, ntries ) ;

      prior_x1 = 0.5 ;             // Arbitrary
      for (i=0 ; i<nsamps ; i++) { // Create bivariate sample with known correlation
         if (unifrand() < ptie)    // Duplicate the prior observation for a tie?
            x1 = prior_x1 ;
         else {
            x1 = normal () ;
            prior_x1 = x1 ;
            }
         x2 = normal () ;
         if (i < nsamps/2) {       // Equally split ties between X and Y
            x[i] = x1 ;
            y[i] = corr * x1 + sqrt ( 1.0 - corr * corr ) * x2 ;
            }
         else {
            y[i] = x1 ;
            x[i] = corr * x1 + sqrt ( 1.0 - corr * corr ) * x2 ;
            }
         }

      mi_adapt = new MutualInformationAdaptive ( nsamps , y , respect_ties , chi_test ) ;
      result = mi_adapt->mut_inf ( x , respect_ties ) ;
      delete mi_adapt ;
      total_adapt += result ;
      bias_adapt += result - correct ;
      stderr_adapt += (result - correct) * (result - correct) ;

      mi_parzen = new MutualInformationParzen ( nsamps , y , ndiv ) ;
      result = mi_parzen->mut_inf ( x ) ;
      delete mi_parzen ;
      total_parzen += result ;
      bias_parzen += result - correct ;
      stderr_parzen += (result - correct) * (result - correct) ;

      if ((((itry-1) % divisor) == 0)
       || (itry == ntries) ) {        // Don't do this every try!  Too slow.
         printf ( "\nParzen Mean = %.5lf   Bias = %.5lf   StdErr = %.5lf",
            total_parzen/itry, bias_parzen/itry, sqrt ( stderr_parzen/itry )) ;
         printf ( "\nAdapt  Mean = %.5lf   Bias = %.5lf   StdErr = %.5lf",
               total_adapt/itry, bias_adapt/itry, sqrt ( stderr_adapt/itry )) ;
         }

      if (_kbhit ()) {         // Has the user pressed a key?
         if (_getch() == 27)   // The ESCape key?
            break ;
         }

      } // For all tries

   free ( x ) ;
   free ( y ) ;
   return EXIT_SUCCESS ;
}
