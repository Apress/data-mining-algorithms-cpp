/******************************************************************************/
/*                                                                            */
/*  TEST_DIS - Test the discrete mutual information methods                   */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <conio.h>
#include <ctype.h>
#include <stdlib.h>

extern double normal () ;
extern double unifrand () ;
extern void partition ( int n , double *data , int *npart ,
                        double *bnds , short int *bins ) ;

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

int main (
   int argc ,    // Number of command line arguments (includes prog name)
   char *argv[]  // Arguments (prog name is argv[0])
   )

{
   int i, j, k, nsamps, ntries, itype, divisor, itry, npart ;
   int isplit, nsplits, splits[10], nmiss ;
   short int *xbins, *ybins ;
   double param, ptie, *x, *y, x1, x2, result, prior_x1, p, sum, marg1, marg2 ;
   double ent, denom, cond, low0, low1, high0, high1, missfrac ;
   double right, wrong0, wrong1, cut0, cut1, cut2, cut3, cut4 ;
   double correctMI[10], total[10], bias[10], std_err[10] ;
   double lower0[10], upper0[10], lower1[10], upper1[10], miss[10] ;
   double outside0[10], outside1[10] ;
   MutualInformationDiscrete *mi ;

/*
   Process command line parameters
*/

#if 1
   if (argc != 6) {
      printf ( "\nUsage: TEST_DIS nsamples ntries type parameter ptie" ) ;
      printf ( "\n  nsamples - Number of cases in the dataset" ) ;
      printf ( "\n  ntried - Number of Monte-Carlo replications" ) ;
      printf ( "\n  type - Type of test" ) ;
      printf ( "\n    0=bivariate normal with specified correlation" ) ;
      printf ( "\n    1=discrete bins with uniform error distribution" ) ;
      printf ( "\n    2=discrete bins with triangular error distribution" ) ;
      printf ( "\n    3=discrete bins with cyclic error distribution" ) ;
      printf ( "\n    4=discrete bins with attractive class error distribution" ) ;
      printf ( "\n  parameter - Depends on type of test" ) ;
      printf ( "\n    0 - Correlation" ) ;
      printf ( "\n    >0 - error probability" ) ;
      printf ( "\n  ptie - If typ=0, probability of a tied case, else ignored" ) ;
      exit ( 1 ) ;
      }

   nsamps = atoi ( argv[1] ) ;
   ntries = atoi ( argv[2] ) ;
   itype = atoi ( argv[3] ) ;
   param = atof ( argv[4] ) ;
   ptie = atof ( argv[5] ) ;
#else
   nsamps = 1000 ;
   ntries = 10000 ;
   itype = 2 ;
   param = 0.2 ;
   ptie = 0.0 ;
#endif

   if ((nsamps <= 0)  ||  (ntries <= 0)  ||  (param < 0.0)  ||  (param > 1.0)
    ||  (itype < 0)  ||  (itype > 4)  || (ptie < 0.0)  || (ptie > 1.0)) {
      printf ( "\nUsage: TEST_DIS nsamples ntries type parameter ptie" ) ;
      exit ( 1 ) ;
      }

   if (itype > 0) {
      if (param > 0.5) {
         printf ( "\nNOTE... Reducing P(error) from %.4lf to 0.5", param ) ;
         printf ( "\nPress any key..." ) ;
         param = 0.5 ;
         _getch () ;
         }
      if (param == 0.0)          // Prevent numerical problems
         param = 1.e-14 ;
      if (param == 1.0)
         param = 1.0 - 1.e-14 ;
      }


/*
   Allocate memory and initialize
*/

   divisor = ntries / 100 ;  // This is for progress reports only
   if (divisor < 1)
      divisor = 1 ;

   x = (double *) malloc ( nsamps * sizeof(double) ) ;
   assert ( x != NULL ) ;
   y = (double *) malloc ( nsamps * sizeof(double) ) ;
   assert ( y != NULL ) ;
   xbins = (short int *) malloc ( nsamps * sizeof(short int) ) ;
   assert ( xbins != NULL ) ;
   ybins = (short int *) malloc ( nsamps * sizeof(short int) ) ;
   assert ( ybins != NULL ) ;

/*
   Compute the different numbers of splits
   We increase them by doubling from 2, except that two bins causes various
   problems with the bound algorithms.  So we increase the fist to 3 bins.
*/

   splits[0] = 2 ;
   for (nsplits=1 ; nsplits<10 ; nsplits++) {
      if (nsamps / splits[nsplits-1] < 5)
         break ;
      splits[nsplits] = splits[nsplits-1] * 2 ;
      }
   splits[0] = 3 ;

/*
--------------------------------------------------------------------------------

   Compute the correct mutual information according to the type

--------------------------------------------------------------------------------
*/


/*
   Bivariate normal
*/

   if (itype == 0) {
      for (i=0 ; i<10 ; i++)
         correctMI[i] = -0.5 * log ( 1.0 - param * param ) ;
      }

/*
   Errors are uniformly distributed to all possible error bins
*/

   else if (itype == 1) { // Uniform error distribution
      for (i=0 ; i<nsplits ; i++) {
         j = splits[i] ;  // Number of bins
         p = 1.0 - param ;// Probability of a correct decision
         p /= j ;         // Probability of a given bin being chosen and correct
                          // This is the diagonal of the confusion matrix
         sum = j * p * log(p*j*j) ; // Diagonal
         p = param ;       // Probability of error (off diagonal)
         p /= j * (j-1) ;  // Probability of a given bin being chosen and wrong
                           // This is the off-diagonal elements
         sum += j * (j-1) * p * log(p*j*j) ;
         correctMI[i] = sum ;
         }
      }

/*
   90% of errors go in the upper triangle, 10% in the lower triangle
*/

   else if (itype == 2) { // Triangular error distribution
      for (isplit=0 ; isplit<nsplits ; isplit++) {
         npart = splits[isplit] ; // Number of bins
         right = (1.0 - param) / npart ;
         wrong0 = 0.1 * param / (npart * (npart-1) / 2) ;
         wrong1 = 0.9 * param / (npart * (npart-1) / 2) ;
         sum = 0.0 ;
         for (i=0 ; i<npart ; i++) {
            marg1 = right + i * wrong0 + (npart - 1 - i) * wrong1 ;
            marg2 = right + (npart - 1 - i) * wrong0 ;
            for (j=0 ; j<npart ; j++) {
               if (j < i)
                  sum += wrong0 * log(wrong0/(marg1*marg2)) ;
               else if (j == i)
                  sum += right * log(right/(marg1*marg2)) ;
               else
                  sum += wrong1 * log(wrong1/(marg1*marg2)) ;
               marg2 += wrong1 - wrong0 ;
               }
            }
         correctMI[isplit] = sum ;
         }
      }

/*
   Half of the errors go one bin to the right of the correct bin, and the
   other half go two bins to the right (with wraparound)
*/

   else if (itype == 3) {  // itype=3; Cyclic error distribution
      for (i=0 ; i<nsplits ; i++) {
         j = splits[i] ;  // Number of bins
         p = 1.0 - param ;// Probability of a correct decision
         p /= j ;         // Probability of a given bin being chosen and correct
                          // This is the diagonal of the confusion matrix
         sum = j * p * log(p*j*j) ; // Diagonal
         p = param ;  // Probability of error (off diagonal)
         p /= 2 * j ; // Probability of this adjacent bin being chosen and wrong
         sum += 2 * j * p * log(p*j*j) ;
         correctMI[i] = sum ;
         }
      }

/*
   This is a really complicated test of a couple classes being unnaturally
   attractive.  For the first nbins-2 true classes, most of the errors go to
   the last (rightmost) class, and the rest of the errors go to the second-last
   class.  All other members of the row are zero.
   For the second-last true class, most of the errors go to the last class,
   and the few remaining errors are evenly distributed across the remaining
   classes.  For the last true class, all errors (and it just has a few) are
   evenly distributed across the other classes.
   This tests what happens when most of the errors land in a single class,
   and most of the remaining errors land in a different single class.
*/

   else if (itype == 4) {  // itype=4; Attractive class error distribution
      for (isplit=0 ; isplit<nsplits ; isplit++) {
         npart = splits[isplit] ; // Number of bins
         right = (1.0 - param) / npart ;
         wrong0 = 0.05 * param / ((npart-1) + 2 * (npart-2)) ;
         wrong1 = 0.95 * param / (npart-1) ;
         sum = 0.0 ;
         for (i=0 ; i<npart ; i++) {
            if (i < npart-2) {
               marg1 = right + wrong0 + wrong1 ;
               marg2 = right + 2 * wrong0 ;
               sum += right * log(right/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong0 ;
               sum += wrong0 * log(wrong0/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong1 ;
               sum += wrong1 * log(wrong1/(marg1*marg2)) ;
               }
            else if (i == npart-2) {
               marg1 = right + (npart-2) * wrong0 + wrong1 ;
               marg2 = right + 2.0 * wrong0 ;
               sum += (npart-2) * wrong0 * log(wrong0/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong0 ;
               sum += right * log(right/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong1 ;
               sum += wrong1 * log(wrong1/(marg1*marg2)) ;
               }
            else {
               marg1 = right + (npart-3) * wrong0 ;
               marg2 = right + 2.0 * wrong0 ;
               sum += (npart-2) * wrong0 * log(wrong0/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong0 ;
               sum += wrong0 * log(wrong0/(marg1*marg2)) ;
               marg2 = right + (npart-1) * wrong1 ;
               sum += right * log(right/(marg1*marg2)) ;
               }
            }
         correctMI[isplit] = sum ;
         }
      }

/*
   Main outer loop does all tries
*/

   for (i=0 ; i<nsplits ; i++)
      total[i] = bias[i] = std_err[i] = lower0[i] = upper0[i] =
                 lower1[i] = upper1[i] = miss[i] = outside0[i] = outside1[i] = 0.0 ;

   for (itry=1 ; itry<=ntries ; itry++) {

      if (((itry-1) % divisor) == 0)
         printf ( "\n\n\nTry %d of %d", itry, ntries ) ;

      if (itype == 0) {  // If bivariate normal, generate the data
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
               y[i] = param * x1 + sqrt ( 1.0 - param * param ) * x2 ;
               }
            else {
               y[i] = x1 ;
               x[i] = param * x1 + sqrt ( 1.0 - param * param ) * x2 ;
               }
            }
         }

      for (isplit=0 ; isplit<nsplits ; isplit++) {

         if (itype == 0) {       // Bivariate normal
            npart = splits[isplit] ;
            partition ( nsamps , x , &npart , NULL , xbins ) ;
            npart = splits[isplit] ;
            partition ( nsamps , y , &npart , NULL , ybins ) ;
            }

         else if (itype == 1) {  // Uniform error distribution
            for (i=0 ; i<nsamps ; i++)
               x[i] = unifrand () ;
            npart = splits[isplit] ;
            partition ( nsamps , x , &npart , NULL , xbins ) ;
            for (j=0 ; j<nsamps ; j++) {
               if (unifrand() < param) {
                  for (;;) {  // This is an error
                     ybins[j] = (short int) (0.999999999999 * unifrand() * npart) ;
                     if (xbins[j] != ybins[j]) // Must not accidentally be right!
                        break ;
                     }
                  }
               else   // This is correct
                  ybins[j] = xbins[j] ;
               }
            }

         else if (itype == 2) {  // Triangular error distribution
            npart = splits[isplit] ;
            right = (1.0 - param) / npart ;
            wrong0 = 0.1 * param / (npart * (npart-1) / 2) ; // Lower triangle
            wrong1 = 0.9 * param / (npart * (npart-1) / 2) ; // Upper triangle
            for (j=0 ; j<nsamps ; j++) {
               cut0 = right + (npart-1) * wrong0 ;
               p = unifrand () ;
               for (k=0 ; k<npart ; k++) {
                  if (p < cut0  ||  k == npart-1) {
                     ybins[j] = k ;
                     cut1 = k * wrong1 ;
                     cut2 = cut1 + right ;
                     cut3 = (npart-k-1) * wrong0 ;
                     p = unifrand () * (cut2 + cut3) ;
                     if (p < cut1) {
                        i = (int) (p / cut1 * k) ;
                        xbins[j] = i ;
                        }
                     else if (p < cut2)
                        xbins[j] = k ;
                     else {
                        i = k + (int) (((p - cut2) / cut3) * (npart-k)) ;
                        xbins[j] = i ;
                        }
                     break ;
                     }
                  cut0 += right + (k+1) * wrong1 + (npart-k-2) * wrong0 ;
                  }
               }
            }

         else if (itype == 3) {    // itype == 3 (Cyclic error distribution)
            for (i=0 ; i<nsamps ; i++)
               x[i] = unifrand () ;
            npart = splits[isplit] ;
            partition ( nsamps , x , &npart , NULL , xbins ) ;
            for (j=0 ; j<nsamps ; j++) {
               if (unifrand() < param) {
                  if (unifrand() < 0.5)
                     ybins[j] = (short int) ((xbins[j]+1) % splits[isplit]) ;
                  else
                     ybins[j] = (short int) ((xbins[j]+2) % splits[isplit]) ;
                  }
               else
                  ybins[j] = xbins[j] ;
               }
            }

         else if (itype == 4) {    // itype == 4 (attractive class error distribution)
            npart = splits[isplit] ;
            right = (1.0 - param) / npart ;
            wrong0 = 0.05 * param / ((npart-1) + 2 * (npart-2)) ;
            wrong1 = 0.95 * param / (npart-1) ;
            cut0 = (npart-2) * (right + wrong0 + wrong1) ;
            cut1 = cut0 + (npart-2) * wrong0 + right + wrong1 ;
            cut2 = (npart-2) * wrong0 ;
            cut3 = cut2 + right ;
            cut4 = (npart-1) * wrong0 ;
            for (j=0 ; j<nsamps ; j++) {
               p = unifrand () ;
               if (p < cut0) {
                  k = (int) (p / cut0 * (npart-2)) ;
                  xbins[j] = k ;
                  p = unifrand () * (right + wrong0 + wrong1) ;
                  if (p < right)
                     ybins[j] = k ;
                  else if (p < right + wrong0)
                     ybins[j] = npart-2 ;
                  else
                     ybins[j] = npart-1 ;
                  }
               else if (p < cut1) {
                  xbins[j] = npart-2 ;
                  p = unifrand () * (cut3 + wrong1) ;
                  if (p < cut2) {
                     k = (int) (p / cut2 * (npart-2)) ;
                     ybins[j] = k ;
                     }
                  else if (p < cut3)
                     ybins[j] = npart-2 ;
                  else
                     ybins[j] = npart-1 ;
                  }
               else {
                  xbins[j] = npart-1 ;
                  p = unifrand () * (cut4 + right) ;
                  if (p < cut4) {
                     k = (int) (p / cut4 * (npart-1)) ;
                     ybins[j] = k ;
                     }
                  else
                     ybins[j] = npart-1 ;
                  }
               }
            }

/*
   Create the MutualInformation object.
   Count errors.  This is used only for type 0 (bivariate normal)
*/

         mi = new MutualInformationDiscrete ( nsamps , ybins ) ;
         assert ( mi != NULL ) ;

         nmiss = 0 ;
         for (j=0 ; j<nsamps ; j++) {
            if (xbins[j] != ybins[j])
               ++nmiss ;
            }

         missfrac = (double) nmiss / (double) nsamps ;
         miss[isplit] += missfrac ;

/*
   Compute the mutual information, Y entropy, and conditional entropy
   Tally the mean mutual information and bias and standard error
*/

         result = mi->mut_inf ( xbins ) ; // Mutual information
         ent = mi->entropy () ;           // Y entropy
         cond = ent - result ;            // Conditional entropy H(Y|X)

//         printf ( "\n\nent=%.5lf  cond=%.5lf  MI=%.5lf  hPe=%.5lf  cond_err=%.5lf", /*!!!!!!*/
//                  ent, cond, result, mi->hPe(xbins), mi->conditional_error(xbins)) ; /*!!!!!!*/
//         printf ( "\nnumer0=%.5lf  numer1=%.5lf  lo den=%.5lf  hi den=%.5lf", /*!!!!!!*/
//                  cond - log(2.0), cond - mi->conditional_error ( xbins ),
//                  log(splits[isplit]-1.0), mi->HYe ( xbins )) ; /*!!!!!!*/

         total[isplit] += result ;
         bias[isplit] += result - correctMI[isplit] ;
         std_err[isplit] += (result - correctMI[isplit]) * (result - correctMI[isplit]) ;

/*
   Compute loose and tight lower and upper bounds
*/

         low0 = (cond - log(2.0)) / log ( splits[isplit] - 1.0 ) ;
         low1 = (cond - mi->conditional_error ( xbins )) / log ( splits[isplit] - 1.0 ) ;
         denom = mi->HYe ( xbins ) + 1.e-30 ;
         high0 = cond / denom ;
         high1 = (cond - mi->conditional_error ( xbins )) / denom ;


/*
   Don't allow nonsense lower bound
   Don't go beyond what a naive classifier based on equal priors could do
*/

         if (low0 < 0.0)
            low0 = 0.0 ;

         if (high0 > 1.0 - 1.0 / splits[isplit])
            high0 = 1.0 - 1.0 / splits[isplit] ;

         if (high1 > 1.0 - 1.0 / splits[isplit])
            high1 = 1.0 - 1.0 / splits[isplit] ;

/*
   In rare pathological cases, the limit we just did to the high bound may
   pull it under the low bound.  Prevent this from happening.
*/

         if (low0 > high0)
            low0 = high0 ;

         if (low1 > high1)
            low1 = high1 ;

/*
   Cumulate the mean of the bounds.
*/

         lower0[isplit] += low0 ;
         lower1[isplit] += low1 ;
         upper0[isplit] += high0 ;
         upper1[isplit] += high1 ;

/*
   Count how many times the true population value is outside the computed
   bounds.  Note that I am not aware of any way of computing the expected
   error rate for a bivariate normal, so for the sake of doing something,
   I use the obtained error rate.  Ultimately this will be very good,
   because it will be a reasonably good, asymptotically unbiased Monte-Carlo
   estimator.  Unfortunately, it will take a while to get there, and meanwhile
   outages may be counted.  Expect the outage count to be somewhat inaccurate.
   A better program would not start counting outages until after many replications,
   thus allowing the Monte-Carlo error rate to decently converge before being used.
*/

         if (itype == 0) { // I'm not aware of any simple way to compute true error rate
            if (missfrac < low0  ||  missfrac > high0)
               ++outside0[isplit] ;
            if (missfrac < low1  ||  missfrac > high1)
               ++outside1[isplit] ;
            }

         else {  // We know the true error rate, because it was specified
            if (param < low0  ||  param > high0)
               ++outside0[isplit] ;
            if (param < low1  ||  param > high1)
               ++outside1[isplit] ;
            }

         delete mi ;
         } // For all splits

/*
   Print intermediate results to keep the user happy
*/

      if ((((itry-1) % divisor) == 0) || (itry == ntries) ) { // Don't do this every try!  Too slow.
         if (itry == ntries)
            printf ( "\n\nFinal... n=%d  reps=%d  type=%d  param=%.4lf  ptie=%.4lf\n",
                     nsamps, ntries, itype, param, ptie) ;
         printf ( "\nSplits size  Est. MI  True MI   Bias   StdErr     Lower   Upper   Outside" ) ;
         for (i=0 ; i<nsplits ; i++) {
            printf ( "\n%4d %6d %8.4lf %8.4lf %7.4lf %7.4lf  %8.4lf %7.4lf   %6.3lf",
               splits[i], nsamps/splits[i], total[i]/itry, correctMI[i],
               bias[i]/itry, sqrt ( std_err[i]/itry ),
               lower0[i]/itry, upper0[i]/itry, outside0[i]/itry ) ;
            printf ( "\n                                               %8.4lf %7.4lf   %6.3lf",
               lower1[i]/itry, upper1[i]/itry, outside1[i]/itry ) ;
            }
         }

      if (_kbhit ()) {         // Has the user pressed a key?
         if (_getch() == 27)   // The ESCape key?
            break ;
         }

      } // For all tries

   free ( x ) ;
   free ( y ) ;
   free ( xbins ) ;
   free ( ybins ) ;
   return EXIT_SUCCESS ;
}
