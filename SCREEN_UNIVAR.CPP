/******************************************************************************/
/*                                                                            */
/*  SCREEN_UNIVAR - Univariate screening                                      */
/*                                                                            */
/******************************************************************************/

#define STRICT
#include <windows.h>
#include <commctrl.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <ctype.h>
#include <malloc.h>
#include <new.h>
#include <float.h>
#include <process.h>

#include "\datamine\datamine.rh"
#include "\datamine\const.h"
#include "\datamine\classes.h"
#include "\datamine\extern.h"
#include "\datamine\funcdefs.h"

/*
   The overall algorithm is as follows:

   Allocate working memory and any objects that are universally needed
   Fetch all selected candidates and target from database
   Perform any required initial calculations, such as finding bin boundaries and counts
   For irep=0 to requested Monte-Carlo replications
      Shuffle the target if we are past the first (unshuffled) replication
      Allocate any objects that are dependent on the order of the targets
      For all threads, set thread parameters (thread_params) that are the same for all threads

      n_threads = 0
      ivar = 0
      empty_slot = -1

      Start thread loop

         if (ivar < n_candidates)
            if (empty_slot < 0)
               k = n_threads ;
            else
               k = empty_slot ;
            thread_params[k].ivar = ivar
            thread_params[k].(other stuff) = whatever
            threads[k] = newly created thread
            ++n_threads
            ++ivar

         if n_threads == 0
            Break out of thread loop

         if (n_threads == max_threads  &&  ivar < n_candidates)
            finished_id = ID of the first thread to finish
            criterion[thread_params[finished_id].ivar] = thread_params[finished_id].criterion
            empty_slot = finished_id
            close thread 'finished_id'
            --n_threads
            
         else if (ivar == n_candidates)
            Wait for all n_threads remaining threads to finish
            for (i=0 ; i<n_threads ; i++)
               criterion[thread_params[i].ivar] = thread_params[i].criterion
               close thread 'i'
            Break out of thread loop

         End of thread loop

      Free any objects that are dependent on the order of the targets

      For ivar=0 to n_candidates

         if (irep == 0)
            sorted_crits[ivar] = original_crits[ivar] = crit[ivar]
            index[ivar] = ivar
            mcpt_bestof[ivar] = mcpt_solo[ivar] = 1
            }

         else if (crit[ivar] >= original_crits[ivar])
            ++mcpt_solo[ivar]

         End of 'for all candidates' loop

      if (irep == 0)
         Sort 'sorted_crits' ascending, simultaneously moving 'index'

      else
         best_crit = criterion[0] ;
         For ivar=1 to n_candidates
            if (criterion[ivar] > best_crit)
               best_crit = criterion[ivar] ;
            End of 'for candidates' loop

         For ivar=0 to n_candidates
            if (best_crit >= original_crits[ivar])
               ++mcpt_bestof[ivar]
            End of 'for all candidates' loop

      End of MCPT replications loop

   for (i=n_candidates-1 ; i>=0 ; i--)
      k = index[i] ;
      Print name, criterion, and mcpt probabilities for candidate k
      End of 'for n_candidates' counting down loop
*/


/*
--------------------------------------------------------------------------------

   Subroutine to compute discrete mutual information

--------------------------------------------------------------------------------
*/

static double compute_mi (
   int ncases ,                 // Number of cases
   int nbins_pred ,             // Number of predictor bins
   int *pred_bin ,              // Ncases vector of predictor bin indices
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices
   double *pred_marginal ,      // Predictor marginal
   double *target_marginal ,    // Target marginal
   int *bin_counts              // Work area nbins_pred*nbins_target long
   )
{
   int i, j ;
   double px, py, pxy, MI ;

   for (i=0 ; i<nbins_pred ; i++) {      // Zero bin counts
      for (j=0 ; j<nbins_target ; j++)
         bin_counts[i*nbins_target+j] = 0 ;
      }

   for (i=0 ; i<ncases ; i++)
      ++bin_counts[pred_bin[i]*nbins_target+target_bin[i]] ;

   MI = 0.0 ;
   for (i=0 ; i<nbins_pred ; i++) {
      px = pred_marginal[i] ;
      for (j=0 ; j<nbins_target ; j++) {
         py = target_marginal[j] ;
         pxy = (double) bin_counts[i*nbins_target+j] / (double) ncases ;
         if (pxy > 0.0)
            MI += pxy * log ( pxy / (px * py) ) ;
         }
      }

   return MI ;
}


/*
--------------------------------------------------------------------------------

   Subroutine to compute uncertainty reduction

--------------------------------------------------------------------------------
*/

static double compute_ur (
   int ncases ,                 // Number of cases
   int nbins_pred ,             // Number of predictor bins
   int *pred_bin ,              // Ncases vector of predictor bin indices
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices
   double *pred_marginal ,      // Predictor marginal
   double *target_marginal ,    // Target marginal
   int *bin_counts              // Work area nbins_pred*nbins_target long
   )
{
   int i, irow, icol ;
   double p, numer, Hpred, Htarg, Ujoint, UR ;

   for (irow=0 ; irow<nbins_pred ; irow++) {      // Zero bin counts
      for (icol=0 ; icol<nbins_target ; icol++)
         bin_counts[irow*nbins_target+icol] = 0 ;
      }

   for (i=0 ; i<ncases ; i++)
      ++bin_counts[pred_bin[i]*nbins_target+target_bin[i]] ;


   Hpred = 0.0 ;
   for (irow=0 ; irow<nbins_pred ; irow++) {
      p = pred_marginal[irow] ;
      if (p > 0.0)
         Hpred -= p * log ( p ) ;
      }

   Htarg = 0.0 ;
   for (icol=0 ; icol<nbins_target ; icol++) {
      p = target_marginal[icol] ;
      if (p > 0.0)
         Htarg -= p * log ( p ) ;
      }

   Ujoint = 0.0 ;
   for (irow=0 ; irow<nbins_pred ; irow++) {
      for (icol=0 ; icol<nbins_target ; icol++) {
         if (bin_counts[irow*nbins_target+icol]) {
            p = (double) bin_counts[irow*nbins_target+icol] / (double) ncases ;
            Ujoint -= p * log ( p ) ;
            }
         }
      }

   numer = Hpred + Htarg - Ujoint ;
   if (Htarg > 0)
      UR = numer / Htarg ;
   else
      UR = 0.0 ;

   return UR ;
}


/*
--------------------------------------------------------------------------------

   Subroutine to compute Cramer's V

--------------------------------------------------------------------------------
*/

static double compute_V (
   int ncases ,                 // Number of cases
   int nbins_pred ,             // Number of predictor bins
   int *pred_bin ,              // Ncases vector of predictor bin indices
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices
   double *pred_marginal ,      // Predictor marginal
   double *target_marginal ,    // Target marginal
   int *bin_counts              // Work area nbins_pred*nbins_target long
   )
{
   int i, j ;
   double diff, expected, chisq, V ;

   for (i=0 ; i<nbins_pred ; i++) {      // Zero bin counts
      for (j=0 ; j<nbins_target ; j++)
         bin_counts[i*nbins_target+j] = 0 ;
      }

   for (i=0 ; i<ncases ; i++)
      ++bin_counts[pred_bin[i]*nbins_target+target_bin[i]] ;

   chisq = 0.0 ;
   for (i=0 ; i<nbins_pred ; i++) {
      for (j=0 ; j<nbins_target ; j++) {
         expected = pred_marginal[i] * target_marginal[j] * ncases ;
         diff = bin_counts[i*nbins_target+j] - expected ;
         chisq += diff * diff / (expected + 1.e-20) ;
         }
      }

   V = chisq / ncases ;
   if (nbins_pred < nbins_target)
      V /= nbins_pred - 1 ;
   else
      V /= nbins_target - 1 ;

   V = sqrt ( V ) ;

   return V ;
}


/*
--------------------------------------------------------------------------------

   Subroutine to compute Pearson (ordinary) correlation R

--------------------------------------------------------------------------------
*/

static double compute_r (
   int ncases ,              // Number of cases (rows) in data matrix
   int varnum ,              // Column of predictor in database
   int n_vars ,              // Number of columns in database
   double *data ,            // The data is here; ncases rows by n_vars columns
   double *target            // The target (ncases long)
   )
{
   int icase ;
   double xdiff, ydiff, xmean, ymean, xvar, yvar, xy ;

   xmean = ymean = 0.0 ;
   for (icase=0 ; icase<ncases ; icase++) {
      xmean += data[icase*n_vars+varnum] ;
      ymean += target[icase] ;
      }
   xmean /= ncases ;
   ymean /= ncases ;

   xvar = yvar = xy = 1.e-30 ;
   for (icase=0 ; icase<ncases ; icase++) {
      xdiff = data[icase*n_vars+varnum] - xmean ;
      ydiff = target[icase] - ymean ;
      xvar += xdiff * xdiff ;
      yvar += ydiff * ydiff ;
      xy += xdiff * ydiff ;
      }

   return xy / sqrt ( xvar * yvar ) ;
}


/*
--------------------------------------------------------------------------------

   Subroutine to compute Spearman rho

--------------------------------------------------------------------------------
*/

static double compute_rho (  // Returns Spearman rho in range -1 to 1
   int ncases ,       // Number of cases (rows) in data matrix
   int varnum ,       // Column of predictor in database
   int n_vars ,       // Number of columns in database
   double *data ,     // The data is here; ncases rows by n_vars columns
   double *target ,   // The target (ncases long)
   double *x ,        // Work vector ncases long
   double *y          // Work vector ncases long
   )
{
   int icase, j, k, ntied ;
   double val, x_tie_correc, y_tie_correc ;
   double dn, ssx, ssy, rank, diff, rankerr, rho ;

   // We need to rearrange input vectors, so copy them to work vectors
   // To avoid disturbing the caller
   for (icase=0 ; icase<ncases ; icase++) {
      x[icase]= data[icase*n_vars+varnum] ;
      y[icase] = target[icase] ;
      }

   // Compute ties in x, compute correction as SUM ( ties**3 - ties )
   // The following routine sorts x ascending and simultaneously moves y
   qsortds ( 0 , ncases-1 , x , y ) ;
   x_tie_correc = 0.0 ;
   for (j=0 ; j<ncases ; ) { // Convert x to ranks, cumulate tie corec
      val = x[j] ;
      for (k=j+1 ; k<ncases ; k++) {  // Find all ties
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
   qsortds ( 0 , ncases-1 , y , x ) ;
   y_tie_correc = 0.0 ;
   for (j=0 ; j<ncases ; ) { // Convert y to ranks, cumulate tie corec
      val = y[j] ;
      for (k=j+1 ; k<ncases ; k++) {  // Find all ties
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
   dn = ncases ;
   ssx = (dn * dn * dn - dn - x_tie_correc) / 12.0 ;
   ssy = (dn * dn * dn - dn - y_tie_correc) / 12.0 ;
   rankerr = 0.0 ;
   for (j=0 ; j<ncases ; j++) { // Cumulate squared rank differences
      diff = x[j] - y[j] ;
      rankerr += diff * diff ;
      }
   rho = 0.5 * (ssx + ssy - rankerr) / sqrt (ssx * ssy + 1.e-20) ;
   return rho ;
}


/*
--------------------------------------------------------------------------------

   Subroutine to compute quadratic Rsquare

--------------------------------------------------------------------------------
*/

static double compute_quad (
   SingularValueDecomp *sptr , // Used for finding optimal coefficients
   int ncases ,                // Number of cases (rows) in data matrix
   int varnum ,                // Column of predictor in database
   int n_vars ,                // Number of columns in database
   double *data ,              // The data is here; ncases rows by n_vars columns
   double *target              // The target (ncases long)
   )
{
   int icase ;
   double xdiff, ydiff, xmean, ymean, xstd, ystd ;
   double *aptr, *bptr, coefs[3], sum, mse ;

/*
   Standardize the data for stability and simplified calculation
*/

   xmean = ymean = 0.0 ;
   for (icase=0 ; icase<ncases ; icase++) {
      xmean += data[icase*n_vars+varnum] ;
      ymean += target[icase] ;
      }
   xmean /= ncases ;
   ymean /= ncases ;

   xstd = ystd = 1.e-30 ;
   for (icase=0 ; icase<ncases ; icase++) {
      xdiff = data[icase*n_vars+varnum] - xmean ;
      ydiff = target[icase] - ymean ;
      xstd += xdiff * xdiff ;
      ystd += ydiff * ydiff ;
      }

   xstd = sqrt ( xstd / ncases ) ;
   ystd = sqrt ( ystd / ncases ) ;

/*
   Fill in SingularValueDecomp object and compute optimal coefficients
*/

   aptr = sptr->a ;
   bptr = sptr->b ;

   for (icase=0 ; icase<ncases ; icase++) {
      xdiff = (data[icase*n_vars+varnum] - xmean) / xstd ;
      ydiff = (target[icase] - ymean) / ystd ;
      *aptr++ = xdiff * xdiff ;  // Quadratic term
      *aptr++ = xdiff ;          // Linear term
      *aptr++ = 1.0 ;            // Constant term
      *bptr++ = ydiff ;          // Predicted value
      }

   sptr->svdcmp () ;
   sptr->backsub ( 1.e-7 , coefs ) ;

/*
   Compute the error
*/

   mse = 0.0 ;

   for (icase=0 ; icase<ncases ; icase++) {
      xdiff = (data[icase*n_vars+varnum] - xmean) / xstd ;
      ydiff = (target[icase] - ymean) / ystd ;
      sum = coefs[0] * xdiff * xdiff + coefs[1] * xdiff + coefs[2] ;
      ydiff -= sum ;   // True minus predicted
      mse += ydiff * ydiff ;
      }

   return 1.0 - mse /ncases ;
}


/*
--------------------------------------------------------------------------------

   This routine is called from CSCV.CPP for computing fold performance

--------------------------------------------------------------------------------
*/

void univar_cscv_crit ( LPVOID dp )
{
   double crit ;
   MutualInformationAdaptive *mi_adapt ;

   if (((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_CONTINUOUS) {
      if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_CMI) {
         mi_adapt = ((UNIVAR_CRIT_PARAMS *) dp)->mi_adapt ;
         crit = mi_adapt->compute_mut_inf ( ((UNIVAR_CRIT_PARAMS *) dp)->database , 1 ,
                                            ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                                            ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ) ;
         }
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_R)
         crit = compute_r ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_RHO)
         crit = compute_rho ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->target ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->work1 ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->work2 ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_QUAD)
         crit = compute_quad ( ((UNIVAR_CRIT_PARAMS *) dp)->sptr ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->target ) ;
      }

   else if (((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_TAILS
         || ((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_DISCRETE) {
      if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_DMI)
         crit = compute_mi ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_UNCERT)
         crit = compute_ur ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_V)
         crit = compute_V ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else
         assert ( 2 == 3 ) ;
      }

   else
      assert ( 1 == 2 ) ;

   ((UNIVAR_CRIT_PARAMS *) dp)->crit = crit ;
}


/*
--------------------------------------------------------------------------------

   This is practically identical to the routine above.
   However, this is stdcall for thread use.

--------------------------------------------------------------------------------
*/


static unsigned int __stdcall univar_threaded ( LPVOID dp )
{
   double crit ;
   MutualInformationAdaptive *mi_adapt ;

   if (((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_CONTINUOUS) {
      if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_CMI) {
         mi_adapt = ((UNIVAR_CRIT_PARAMS *) dp)->mi_adapt ;
         crit = mi_adapt->compute_mut_inf ( ((UNIVAR_CRIT_PARAMS *) dp)->database , 1 ,
                                            ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                                            ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ) ;
         }
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_R)
         crit = compute_r ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_RHO)
         crit = compute_rho ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->target ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->work1 ,
                              ((UNIVAR_CRIT_PARAMS *) dp)->work2 ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_QUAD)
         crit = compute_quad ( ((UNIVAR_CRIT_PARAMS *) dp)->sptr ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->varnum ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->n_vars ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->database ,
                               ((UNIVAR_CRIT_PARAMS *) dp)->target ) ;
      }

   else if (((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_TAILS
         || ((UNIVAR_CRIT_PARAMS *) dp)->type == SCREEN_UNIVAR_DISCRETE) {
      if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_DMI)
         crit = compute_mi ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_UNCERT)
         crit = compute_ur ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                             ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else if (((UNIVAR_CRIT_PARAMS *) dp)->subtype == SCREEN_UNIVAR_V)
         crit = compute_V ( ((UNIVAR_CRIT_PARAMS *) dp)->ncases ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->nbins_pred ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->pred_bin ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->nbins_target ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target_bin ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->pred_marginal ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->target_marginal ,
                            ((UNIVAR_CRIT_PARAMS *) dp)->bin_counts ) ;
      else
         assert ( 2 == 3 ) ;
      }

   else
      assert ( 1 == 2 ) ;

   ((UNIVAR_CRIT_PARAMS *) dp)->crit = crit ;
   return 0 ;
}

int screen_univar (
   int type ,         // Type of study (SCREEN_UNIVAR_? in CONST.H): continuous, tails, discrete)
   int subtype ,      // Subtype of study (SCREEN_UNIVAR_? in CONST.H; mutual info, uncertainty reduction, etc)
   int npred ,        // Number of predictors
   int *preds ,       // Their indices are here
   int targetvar ,    // Index of target variable
   int nbins_pred ,   // Number of predictor bins
   int nbins_target , // Number of target bins, 0 for 2 sign-based bins
   double tail_frac , // Tail fraction (0 to 0.5) if nbins_pred=0, else ignored
   int CSCV_subsets , // Number of CSCV subsets, 0 for no CSCV
   int mcpt_type ,    // 1=complete, 2=cyclic
   int mcpt_reps      // Number of MCPT replications, <=1 for no MCPT
   )
{
   int i, j, k, n, ret_val, ivar, irep, varnum, *index, ithread, n_threads, max_threads, empty_slot ;
   int *mcpt_solo, *mcpt_bestof, *tail_n ;
   int *pred_bin, *target_bin, *work_bin, *target_bin_ptr, *bin_counts ;
   int need_target_thresholds, need_pred_bin, need_work_bin, need_target_bin, need_pred_thresholds, need_bin_counts ;
   int *cscv_indices, *cscv_lengths, *cscv_flags, *cscv_sorted_index, half_S ;
   int *cscv_iwork_pred, *cscv_iwork_targ ;
   double *pred, *work_target, *target, *pred_thresholds, *target_thresholds ;
   double *pred_bounds, *target_bounds, *crit, *original_crits, *sorted_crits, best_crit ;
   double *pred_marginal, *target_marginal, dtemp, *work1, *work2 ;
   double *cscv_crits, *cscv_indep, *cscv_is_crits, *cscv_oos_crits, *cscv_work_pred, *cscv_work_targ ;
   char msg[256], msg2[256] ;
   SingularValueDecomp *sptr[MAX_THREADS] ;
   MutualInformationAdaptive *mi_adapt[MAX_THREADS] ;
   UNIVAR_CRIT_PARAMS univar_params[MAX_THREADS] ;
   HANDLE threads[MAX_THREADS] ;

   pred = NULL ;
   crit = NULL ;
   index = NULL ;
   pred_thresholds = NULL ;
   target_thresholds = NULL ;
   pred_bin = NULL ;
   bin_counts = NULL ;
   work1 = work2 = NULL ;

   CSCV_subsets = (CSCV_subsets + 1) / 2 * 2 ;   // If user specified odd, bump up to even
   if (type == SCREEN_UNIVAR_TAILS)
      CSCV_subsets = 0 ;              // This was also done in dialog, so redundant
   half_S = CSCV_subsets / 2 ;

   ret_val = 0 ;

   max_threads = MAX_THREADS ;
   if (max_threads > npred)
      max_threads = npred ;

/*
   Print user-specified parameters
*/

   audit ( "" ) ;
   audit ( "" ) ;
   audit ( "******************************************************************************" ) ;
   audit ( "*                                                                            *" ) ;
   if (type == SCREEN_UNIVAR_CONTINUOUS) {
      if (subtype == SCREEN_UNIVAR_CMI)
         audit ( "* Continuous univariate mutual information (one predictor, one target)       *" ) ;
      else if (subtype == SCREEN_UNIVAR_R)
         audit ( "* Pearson's r (ordinary correlation coefficient)                             *" ) ;
      else if (subtype == SCREEN_UNIVAR_RHO)
         audit ( "* Spearman rho (nonparametric correlation coefficient)                       *" ) ;
      else if (subtype == SCREEN_UNIVAR_QUAD)
         audit ( "* Quadratic R-squared                                                        *" ) ;
      }
   else if (type == SCREEN_UNIVAR_TAILS) {
      if (subtype == SCREEN_UNIVAR_DMI)
         audit ( "* Tails-only univariate mutual information (one predictor, one target)       *" ) ;
      else if (subtype == SCREEN_UNIVAR_UNCERT)
         audit ( "* Tails-only univariate uncertainty reduction                                *" ) ;
      else if (subtype == SCREEN_UNIVAR_V)
         audit ( "* Tails-only univariate Cramer's V                                           *" ) ;
      sprintf_s ( msg, "*     %5.3lf predictor tails used                                             *", tail_frac ) ;
      audit ( msg ) ;
      sprintf_s ( msg, "*    %2d target bins                                                          *", nbins_target ) ;
      audit ( msg ) ;
      }
   else if (type == SCREEN_UNIVAR_DISCRETE) {
      if (subtype == SCREEN_UNIVAR_DMI)
         audit ( "* Discrete univariate mutual information                                     *" ) ;
      else if (subtype == SCREEN_UNIVAR_UNCERT)
         audit ( "* Discrete univariate uncertainty reduction                                  *" ) ;
      else if (subtype == SCREEN_UNIVAR_V)
         audit ( "* Discrete univariate Cramer's V                                             *" ) ;
      sprintf_s ( msg, "*    %2d predictor bins                                                       *", nbins_pred ) ;
      audit ( msg ) ;
      sprintf_s ( msg, "*    %2d target bins                                                          *", nbins_target ) ;
      audit ( msg ) ;
      }
   sprintf_s ( msg, "* %5d predictor candidates                                                 *", npred ) ;
   audit ( msg ) ;
   if (CSCV_subsets > 0) {
      sprintf_s ( msg, "*   %3d CSCV subsets                                                         *", CSCV_subsets ) ;
      audit ( msg ) ;
      }
   if (mcpt_reps > 1) {
      if (mcpt_type == 1)
         sprintf_s ( msg, "* %5d replications of complete Monte-Carlo Permutation Test                *", mcpt_reps ) ;
      else if (mcpt_type == 2)
         sprintf_s ( msg, "* %5d replications of cyclic Monte-Carlo Permutation Test                  *", mcpt_reps ) ;
      audit ( msg ) ;
      }
   else {
      sprintf_s ( msg, "*       No Monte-Carlo Permutation Test                                      *" ) ;
      audit ( msg ) ;
      }
   audit ( "*                                                                            *" ) ;
   audit ( "******************************************************************************" ) ;


/*
   Allocate memory
*/

   pred = (double *) malloc ( 3 * n_cases * sizeof(double) ) ;  // Pred, work_target, target
   work_target = pred + n_cases ;
   target = work_target + n_cases ;

   crit = (double *) malloc ( 3 * npred * sizeof(double) ) ;  // Crit, original_crits, sorted_crits
   original_crits = crit + npred ;
   sorted_crits = original_crits + npred ;

   index = (int *) malloc ( 4 * npred * sizeof(int) ) ;   // Index, mcpt_solo, mcpt_bestof, tail_n
   mcpt_solo = index + npred ;
   mcpt_bestof = mcpt_solo + npred ;
   tail_n = mcpt_bestof + npred ;

   work1 = (double *) malloc ( max_threads * n_cases * sizeof(double) ) ;
   work2 = (double *) malloc ( max_threads * n_cases * sizeof(double) ) ;

   // If DISCRETE, we use only nbins_pred-1 thresholds, but allocate this way for simplicity
   if (type == SCREEN_UNIVAR_TAILS  ||  type == SCREEN_UNIVAR_DISCRETE) {
      pred_thresholds = (double *) malloc ( 2 * nbins_pred * npred * sizeof(double) ) ; // pred_thresholds, pred_marginal
      pred_marginal = pred_thresholds + npred * nbins_pred ;
      need_pred_thresholds = 1 ;
      }
   else {
      pred_thresholds = NULL ;
      need_pred_thresholds = 0 ;
      }

   // If TAILS we compute the target thresholds and bins separately for each predictor
   if (type == SCREEN_UNIVAR_TAILS) {
      pred_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ;
      work_bin = (int *) malloc ( n_cases * sizeof(int) ) ;
      target_thresholds = (double *) malloc ( 2 * nbins_target * npred * sizeof(double) ) ; // target_thresholds, target_marginal
      target_marginal = target_thresholds + nbins_target * npred ;
      target_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ; // Target bin separate for each predictor
      bin_counts = (int *) malloc ( max_threads * nbins_pred * nbins_target * sizeof(int) ) ;
      need_target_thresholds = 1 ;
      need_pred_bin = 1 ;
      need_work_bin = 1 ;
      need_target_bin = 1 ;
      need_bin_counts = 1 ;
      }
   else if (type == SCREEN_UNIVAR_DISCRETE) {
      pred_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ;
      work_bin = (int *) malloc ( n_cases * sizeof(int) ) ;
      target_thresholds = (double *) malloc ( 2 * nbins_target * sizeof(double) ) ; // target_thresholds, target_marginal
      target_marginal = target_thresholds + nbins_target ;
      target_bin = (int *) malloc ( n_cases * sizeof(int) ) ; // Target bin the same for all predictors
      bin_counts = (int *) malloc ( max_threads * nbins_pred * nbins_target * sizeof(int) ) ;
      need_target_thresholds = 1 ;
      need_pred_bin = 1 ;
      need_work_bin = 1 ;
      need_target_bin = 1 ;
      need_bin_counts = 1 ;
      }
   else {
      target_thresholds = NULL ;
      need_target_thresholds = 0 ;
      pred_bin = NULL ;
      need_pred_bin = 0 ;
      work_bin = NULL ;
      need_work_bin = 0 ;
      target_bin = NULL ;
      need_target_bin = 0 ;
      need_bin_counts = 0 ;
      }

/*
   These allocs are exclusively for CSCV
*/

   if (half_S) {
      cscv_crits = (double *) malloc ( 3 * npred * sizeof(double) ) ;
      cscv_is_crits = cscv_crits + npred ;
      cscv_oos_crits = cscv_is_crits + npred ;
      cscv_indices = (int *) malloc ( (3 * 2 * half_S + npred) * sizeof(int) ) ;
      cscv_lengths = cscv_indices + 2 * half_S ;
      cscv_flags = cscv_lengths + 2 * half_S ;
      cscv_sorted_index = cscv_flags + 2 * half_S ;
      cscv_indep = (double *) malloc ( n_cases * npred * sizeof(double) ) ;
      cscv_work_pred = (double *) malloc ( 2 * n_cases * sizeof(double) ) ;
      cscv_work_targ = cscv_work_pred + n_cases ;
      cscv_iwork_pred = (int *) malloc ( 2 * n_cases * sizeof(int) ) ;
      cscv_iwork_targ = cscv_iwork_pred + n_cases ;
      }
   else {
      cscv_crits = NULL ;
      cscv_indices = NULL ;
      cscv_indep = NULL ;
      cscv_work_pred = NULL ;
      cscv_iwork_pred = NULL ;
      }

   for (i=0 ; i<max_threads ; i++)
      sptr[i] = NULL ;

   if (type == SCREEN_UNIVAR_CONTINUOUS  &&  subtype == SCREEN_UNIVAR_QUAD) {
      for (i=0 ; i<max_threads ; i++) {
         sptr[i] = new SingularValueDecomp ( n_cases , 3 , 0 ) ;
         if (sptr[i] == NULL  ||  ! sptr[i]->ok) {
            for (j=0 ; j<i ; j++) {
               delete sptr[j] ;
               sptr[j] = NULL ;
               }
            ret_val = ERROR_INSUFFICIENT_MEMORY ;
            goto FINISH ;
            }
         }
      }

   if (pred == NULL  ||  crit == NULL  ||  index == NULL
    || work1 == NULL  ||  work2 == NULL
    || (need_pred_thresholds  &&  pred_thresholds == NULL)
    || (need_target_thresholds  &&  target_thresholds == NULL)
    || (need_target_bin  &&  target_bin == NULL)
    || (need_pred_bin  &&  pred_bin == NULL)
    || (need_work_bin  &&  work_bin == NULL)
    || (need_bin_counts  &&  bin_counts == NULL)
    || (half_S  &&  cscv_crits == NULL)
    || (half_S  &&  cscv_indices == NULL)
    || (half_S  &&  cscv_indep == NULL)
    || (half_S  &&  cscv_work_pred == NULL)
    || (half_S  &&  cscv_iwork_pred == NULL)) {
      ret_val = ERROR_INSUFFICIENT_MEMORY ;
      goto FINISH ;
      }


/*
   Make an initial pass through the data to find predictor thresholds and
   permanently save bin indices for predictors and target.
   If tails-only, we must save the associated target subset indices, separately for each predictor.
   If not tails only, do target when ivar=-1.
   The continuous case is handled first; only the target needs to be saved.
*/

   if (type == SCREEN_UNIVAR_CONTINUOUS) {    // If continuous, no bounds at all are needed
      for (i=0 ; i<n_cases ; i++)             // Extract target from database
         target[i] = database[i*n_vars+targetvar] ;
      }

   else {  // This handles everything that needs bins

      for (ivar=-1 ; ivar<npred ; ivar++) {
         if (ivar == -1) {                   // If this is target pass
            if (type == SCREEN_UNIVAR_TAILS) // But user specified tails only
               continue ;                    // then we process the targets separately for each predictor's subset
            }
         else
            varnum = preds[ivar] ;

         if (user_pressed_escape()) {
            audit ( "ERROR: User pressed ESCape during univariate screening" ) ;
            ret_val = ERROR_ESCAPE ;
            goto FINISH ;
            }

         // At this point, one of three things holds:
         //   Case 1: ivar=-1 (which implies not TAILS): This is the target
         //   Case 2: ivar>=0, not TAILS: This is a predictor
         //   Case 3: ivar>=0, TAILS: This is a predictor AND we must save the corresponding target

         // ------> Case 1: ivar=-1 (which implies not TAILS): This is the target

         if (ivar == -1) {
            for (i=0 ; i<n_cases ; i++)               // Extract target from database
               target[i] = database[i*n_vars+targetvar] ;
            target_bounds = target_thresholds ;
            k = nbins_target ;
            partition ( n_cases , target , &k , target_bounds , target_bin ) ;
            if (k <nbins_target) {
               sprintf_s ( msg, "ERROR: Numerous ties reduced target bins to %d", k ) ;
               audit ( msg ) ;
               ret_val = ERROR_SYNTAX ;
               goto FINISH ;
               }
            assert ( k == nbins_target ) ;
            tail_n[0] = n_cases ;       // Later code is simplified if we save this as if TAILS
            }

         // ------> Case 2: ivar>=0, not TAILS: This is a predictor

         else if (ivar >= 0  &&  type != SCREEN_UNIVAR_TAILS) {
            for (i=0 ; i<n_cases ; i++)               // Extract predictor from database
               pred[i] = database[i*n_vars+varnum] ;
            pred_bounds = pred_thresholds + ivar * nbins_pred ;
            k = nbins_pred ;
            partition ( n_cases , pred , &k , pred_bounds , pred_bin+ivar*n_cases ) ;
            if (k <nbins_pred) {
               sprintf_s ( msg, "ERROR: Numerous ties reduced predictor %s bins to %d", var_names[preds[ivar]], k ) ;
               audit ( msg ) ;
               ret_val = ERROR_SYNTAX ;
               goto FINISH ;
               }
            assert ( k == nbins_pred ) ;
            }

         // ------> Case 3: ivar>=0, TAILS: This is a predictor AND we must save the corresponding target

         else if (ivar >= 0  &&  type == SCREEN_UNIVAR_TAILS) {
            // Compute predictor bounds per tail fraction
            for (i=0 ; i<n_cases ; i++)               // Extract predictor from database
               pred[i] = database[i*n_vars+varnum] ;
            qsortd ( 0 , n_cases-1 , pred ) ;
            pred_bounds = pred_thresholds + ivar * nbins_pred ;
            k = (int) (tail_frac * (n_cases+1)) - 1 ;
            if (k < 0)
               k = 0 ;
            pred_bounds[0] = pred[k] ;
            pred_bounds[1] = pred[n_cases-1-k] ;
            // Compute and save predictor bin indices; Also save target for soon computing its bounds and indices
            n = 0 ;
            for (i=0 ; i<n_cases ; i++) {
               if (database[i*n_vars+varnum] <= pred_bounds[0])
                  pred_bin[ivar*n_cases+n] = 0 ;
               else if (database[i*n_vars+varnum] >= pred_bounds[1])
                  pred_bin[ivar*n_cases+n] = 1 ;
               else
                  continue ;
               target[n] = database[i*n_vars+targetvar] ;
               ++n ;
               }
            tail_n[ivar] = n ;

            // Compute the target bounds based on this 'predictor tail' subset of the entire dataset
            target_bounds = target_thresholds + ivar * nbins_target ;
            k = nbins_target ;
            partition ( n , target , &k , target_bounds , target_bin+ivar*n_cases ) ;
            if (k <nbins_target) {
               sprintf_s ( msg, "ERROR: Numerous ties reduced target bins to %d", k ) ;
               audit ( msg ) ;
               ret_val = ERROR_SYNTAX ;
               goto FINISH ;
               }
            assert ( k == nbins_target ) ;
            }

         else
            assert ( 1 == 0 ) ;

         } // For ivar (reading each variable)


/*
   All thresholds (predictor and target) are computed and saved.
   The predictor and target bin indices are also saved.
   If not TAILS, the saved target bin indices are based on the entire dataset,
   and the saved target thresholds are similarly for the entire dataset.
   But if TAILS, each predictor candidate will have its own target subset
   and thresholds corresponding to that subset.

   Print the thresholds for the user's edification
*/

      audit ( "" ) ;
      audit ( "" ) ;
      audit ( "The bounds that define bins are now shown" ) ;
      audit ( "" ) ;

      if (type == SCREEN_UNIVAR_TAILS) {
         audit ( "Target bounds are shown (after :) separately for each predictor candidate" ) ;
         audit ( "" ) ;
         audit ( "       Variable  Predictor bounds... : Target bounds" ) ;
         audit ( "" ) ;
         }

      else {
         audit ( "Target bounds are based on the entire dataset..." ) ;
         sprintf_s ( msg , "%12.5lf", target_thresholds[0] ) ;
         for (i=1 ; i<nbins_target-1 ; i++) {
            sprintf_s ( msg2 , "  %12.5lf", target_thresholds[i] ) ;
            strcat_s ( msg , msg2 ) ;
            }

         audit ( msg ) ;
         audit ( "" ) ;
         audit ( "       Variable  Bounds..." ) ;
         audit ( "" ) ;
         }

      for (ivar=0 ; ivar<npred ; ivar++) {
         pred_bounds = pred_thresholds + ivar * nbins_pred ;
         sprintf_s ( msg, "%15s  %12.5lf", var_names[preds[ivar]], pred_bounds[0] ) ;
         k = (type == SCREEN_UNIVAR_TAILS) ? 2 : nbins_pred-1 ;
         for (i=1 ; i<k ; i++) {
            sprintf_s ( msg2 , "  %12.5lf", pred_bounds[i] ) ;
            strcat_s ( msg , msg2 ) ;
            }
         if (type == SCREEN_UNIVAR_TAILS) {
            target_bounds = target_thresholds + ivar * nbins_target ;
            sprintf_s ( msg2 , "  :  %12.5lf", target_bounds[0] ) ;
            strcat_s ( msg , msg2 ) ;
            for (i=1 ; i<nbins_target-1 ; i++) {
               sprintf_s ( msg2 , "  %12.5lf", target_bounds[i] ) ;
               strcat_s ( msg , msg2 ) ;
               }
            } // If TAILS
         audit ( msg ) ;
         } // For all predictors

/*
   Compute marginals
*/

      for (ivar=0 ; ivar<npred ; ivar++) {

         for (i=0 ; i<nbins_pred ; i++)
            pred_marginal[ivar*nbins_pred+i] = 0.0 ;

         if (ivar==0  ||  type == SCREEN_UNIVAR_TAILS) {
            for (i=0 ; i<nbins_target ; i++)
               target_marginal[ivar*nbins_target+i] = 0.0 ;
            }

         for (i=0 ; i<n_cases ; i++) {
            ++pred_marginal[ivar*nbins_pred+pred_bin[ivar*n_cases+i]] ;
            if (type == SCREEN_UNIVAR_TAILS) {
               ++target_marginal[ivar*nbins_target+target_bin[ivar*n_cases+i]] ;
               if (i == tail_n[ivar]-1)
                  break ;
               }
            else if (ivar == 0)                           // Do target just once
               ++target_marginal[target_bin[i]] ;
            } // For all cases
         }

      for (ivar=0 ; ivar<npred ; ivar++) {  // Divide counts by number of cases to get marginal

         if (type == SCREEN_UNIVAR_TAILS) {
            for (i=0 ; i<nbins_pred ; i++)
               pred_marginal[ivar*nbins_pred+i] /= tail_n[ivar] ;
            }
         else {
            for (i=0 ; i<nbins_pred ; i++)
               pred_marginal[ivar*nbins_pred+i] /= n_cases ;
            }

         if (ivar==0  ||  type == SCREEN_UNIVAR_TAILS) {
            for (i=0 ; i<nbins_target ; i++)
               target_marginal[ivar*nbins_target+i] /= tail_n[ivar] ;
            }
         }


/*
   Print the marginals for the user's edification
*/

      audit ( "" ) ;
      audit ( "" ) ;
      audit ( "The marginal distributions are now shown." ) ;
      audit ( "If the data is continuous, the marginals will be nearly equal." ) ;
      audit ( "Widely unequal marginals indicate potentially problematic ties." ) ;
      audit ( "" ) ;

      if (type == SCREEN_UNIVAR_TAILS) {
         audit ( "Target marginals are shown (after :) separately for each predictor candidate" ) ;
         audit ( "" ) ;
         audit ( "       Variable  Predictor marginals... : Target marginals" ) ;
         audit ( "" ) ;
         }

      else {
         audit ( "Target marginals are based on the entire dataset..." ) ;
         sprintf_s ( msg , "%12.5lf", target_marginal[0] ) ;
         for (i=1 ; i<nbins_target ; i++) {
            sprintf_s ( msg2 , "  %12.5lf", target_marginal[i] ) ;
            strcat_s ( msg , msg2 ) ;
            }

         audit ( msg ) ;
         audit ( "" ) ;
         audit ( "       Variable    Marginal..." ) ;
         audit ( "" ) ;
         }

      for (ivar=0 ; ivar<npred ; ivar++) {
         sprintf_s ( msg, "%15s  %12.5lf", var_names[preds[ivar]], pred_marginal[ivar*nbins_pred+0] ) ;
         for (i=1 ; i<nbins_pred ; i++) {
            sprintf_s ( msg2 , "  %12.5lf", pred_marginal[ivar*nbins_pred+i] ) ;
            strcat_s ( msg , msg2 ) ;
            }
         if (type == SCREEN_UNIVAR_TAILS) {
            sprintf_s ( msg2 , "  :  %12.5lf", target_marginal[ivar*nbins_target+0] ) ;
            strcat_s ( msg , msg2 ) ;
            for (i=1 ; i<nbins_target ; i++) {
               sprintf_s ( msg2 , "  %12.5lf", target_marginal[ivar*nbins_target+i] ) ;
               strcat_s ( msg , msg2 ) ;
               }
            } // If TAILS
         audit ( msg ) ;
         } // For all predictors
      } // If a task that needs bins

/*
--------------------------------------------------------------------------------

   Handle CSCV

--------------------------------------------------------------------------------
*/

   if (half_S) {
      title_progbar ( "CSCV..." ) ;
      univar_params[0].type = type ;
      univar_params[0].subtype = subtype ;
      univar_params[0].ncases = n_cases ;
      univar_params[0].work1 = work1 ;
      univar_params[0].work2 = work2 ;
      univar_params[0].database = database ;
      univar_params[0].target = target ;
      univar_params[0].n_vars = n_vars ;
      univar_params[0].nbins_pred = nbins_pred ;
      univar_params[0].nbins_target = nbins_target ;
      univar_params[0].bin_counts = bin_counts ;
      univar_params[0].pred_bin = pred_bin ;
      univar_params[0].target_bin = target_bin ;
      cscv ( &univar_params[0] , npred , preds , half_S , cscv_crits , cscv_indices , cscv_lengths ,
             cscv_flags , cscv_sorted_index , cscv_is_crits , cscv_oos_crits ,
             cscv_work_pred , cscv_work_targ , cscv_iwork_pred , cscv_iwork_targ ) ;
      }

/*
--------------------------------------------------------------------------------

   Outer-most loop does MCPT replications

--------------------------------------------------------------------------------
*/

   if (mcpt_reps < 1)
      mcpt_reps = 1 ;

   for (irep=0 ; irep<mcpt_reps ; irep++) {

/*
   Shuffle target if in permutation run (irep>0)
   This needs to include a variable loop because if TAILS then
   the target depends on the predictor.
   But it also needs to be done BEFORE the main 'compute MI of each predictor'
   loop because the logic of shuffling just once at the start of each
   replication would be excessively complex with threading.
*/


      if (irep) {                        // If doing permuted runs, shuffle
         if (mcpt_type == 1) {      // Complete
            if (type == SCREEN_UNIVAR_CONTINUOUS) {
               i = n_cases ;        // Number remaining to be shuffled
               while (i > 1) {      // While at least 2 left to shuffle
                  j = (int) (unifrand_fast () * i) ;
                  if (j >= i)
                     j = i - 1 ;
                  dtemp = target[--i] ;
                  target[i] = target[j] ;
                  target[j] = dtemp ;
                  }
               } // If not using bins
            else if (type == SCREEN_UNIVAR_TAILS) {   // Each predictor has its own target subset
               for (ivar=0 ; ivar<npred ; ivar++) {
                  target_bin_ptr = target_bin + ivar * n_cases ;
                  i = tail_n[ivar] ;           // Number remaining to be shuffled
                  while (i > 1) {              // While at least 2 left to shuffle
                     j = (int) (unifrand_fast () * i) ;
                     if (j >= i)
                        j = i - 1 ;
                     k = target_bin_ptr[--i] ;
                     target_bin_ptr[i] = target_bin_ptr[j] ;
                     target_bin_ptr[j] = k ;
                     }
                  }
               } // Else if TAILS
            else {
               i = n_cases ;          // Number remaining to be shuffled
               while (i > 1) {        // While at least 2 left to shuffle
                  j = (int) (unifrand_fast () * i) ;
                  if (j >= i)
                     j = i - 1 ;
                  k = target_bin[--i] ;
                  target_bin[i] = target_bin[j] ;
                  target_bin[j] = k ;
                  }
               } // Else discrete using entire dataset
            } // Type 1, Complete
         else if (mcpt_type == 2) { // Cyclic
            if (type == SCREEN_UNIVAR_CONTINUOUS) {
               j = (int) (unifrand_fast () * n_cases) ;
               if (j >= n_cases)
                  j = n_cases - 1 ;
               for (i=0 ; i<n_cases ; i++)
                  work_target[i] = target[(i+j)%n_cases] ;
               for (i=0 ; i<n_cases ; i++)
                  target[i] = work_target[i]  ;

               } // If continuous
            else if (type == SCREEN_UNIVAR_TAILS) {   // Each predictor has its own target subset
               for (ivar=0 ; ivar<npred ; ivar++) {
                  target_bin_ptr = target_bin + ivar * n_cases ;
                  k = tail_n[ivar] ;
                  j = (int) (unifrand_fast () * k) ;
                  if (j >= k)
                     j = k - 1 ;
                  for (i=0 ; i<k ; i++)
                     work_bin[i] = target_bin_ptr[(i+j)%k] ;
                  for (i=0 ; i<k ; i++)
                     target_bin_ptr[i] = work_bin[i]  ;
                  }
               } // Else if TAILS
            else {
               j = (int) (unifrand_fast () * n_cases) ;
               if (j >= n_cases)
                  j = n_cases - 1 ;
               for (i=0 ; i<n_cases ; i++)
                  work_bin[i] = target_bin[(i+j)%n_cases] ;
               for (i=0 ; i<n_cases ; i++)
                  target_bin[i] = work_bin[i]  ;
               } // Else discrete using entire dataset
            } // Type 2, Cyclic
         } // If in permutation run (irep > 0)


/*
   If the user specified 'continuous' then we need to allocate a
   MutualInformationAdaptive object for use by each thread.
   This object is dependent on the target,
   so we must allocate AFTER the target is shuffled.
*/

      if (type == SCREEN_UNIVAR_CONTINUOUS) {
         for (ithread=0 ; ithread<max_threads ; ithread++) {
            if (ithread == 0)
               mi_adapt[ithread] = new MutualInformationAdaptive ( n_cases , target , 1 , 6.0 , NULL , NULL ) ;
             else
               mi_adapt[ithread] = new MutualInformationAdaptive ( n_cases , target , 1 , 6.0 ,
                                                                   mi_adapt[0]->y , mi_adapt[0]->y_tied ) ;
            if (! mi_adapt[ithread]->ok  ||  mi_adapt[ithread] == NULL) {
               for (i=0 ; i<=ithread ; i++) {
                  if (mi_adapt[i] != NULL)
                     delete mi_adapt[i] ;
                  }
               audit ( "ERROR: Insufficient memory for continuous mutual information" ) ;
               ret_val = ERROR_INSUFFICIENT_MEMORY ;
               goto FINISH ;
               }
            }
         }


/*
-----------------------------------------------------------------------------------

   This next major block of code handles threading
   Compute and save mutual information.  Keep track of maximum.

   NOTE ON THREADS... If the thread workload is low, overhead will keep CPU time
                      low.  If debug printing, one will see that only the first
                      thread keeps ending and getting replaced.  Threading behaves
                      as expected only when each thread uses a lot of CPU time.

-----------------------------------------------------------------------------------
*/



/*
   Initialize those thread parameters which are constant for all threads.
   (To keep things simple, we also do a few things that will be changed later if TAILS.)
   Each thread will have its own private MutualInformationAdaptive object if continuous.
   Else each thread will have its own private bin_count matrix for working storage.
*/

      for (ithread=0 ; ithread<max_threads ; ithread++) {
         univar_params[ithread].type = type ;
         univar_params[ithread].subtype = subtype ;
         univar_params[ithread].ncases = n_cases ;    // TAILS will change this later
         univar_params[ithread].database = database ; // Bin stuff does not use this and next two
         univar_params[ithread].n_vars = n_vars ;
         univar_params[ithread].target = target ;
         univar_params[ithread].work1 = work1 + ithread * n_cases ;
         univar_params[ithread].work2 = work2 + ithread * n_cases ;
         if (type == SCREEN_UNIVAR_CONTINUOUS) {
            univar_params[ithread].mi_adapt = mi_adapt[ithread] ;
            univar_params[ithread].sptr = sptr[ithread] ;
            }
         else if (type == SCREEN_UNIVAR_TAILS  ||  type == SCREEN_UNIVAR_DISCRETE) {
            univar_params[ithread].nbins_pred = nbins_pred ;
            univar_params[ithread].nbins_target = nbins_target ;
            univar_params[ithread].bin_counts = bin_counts + ithread * nbins_pred * nbins_target ;
            univar_params[ithread].target_bin = target_bin ;            // TAILS will change this later
            univar_params[ithread].target_marginal = target_marginal ;  // TAILS will change this later
            }
         } // For all threads, initializing constant stuff


/*
   Do it
*/

      n_threads = 0 ;                    // Counts threads that are active
      for (i=0 ; i<max_threads ; i++)
         threads[i] = NULL ;


      ivar = 0 ;         // Index of predictor in preds
      empty_slot = -1 ;  // After full, will identify the thread that just completed
      for (;;) {         // Main thread loop processes all predictors

/*
   Handle user ESCape
*/

         if (escape_key_pressed  ||  user_pressed_escape ()) {
            for (i=0, k=0 ; i<max_threads ; i++) {
               if (threads[i] != NULL)
                  threads[k++] = threads[i] ;
               }
            ret_val = WaitForMultipleObjects ( n_threads , threads , TRUE , 50000 ) ;
            for (i=0 ; i<n_threads ; i++)
               CloseHandle ( threads[i] ) ;
            if (type == SCREEN_UNIVAR_CONTINUOUS) {
               for (ithread=0 ; ithread<max_threads ; ithread++)
                  delete mi_adapt[ithread] ;
               }
            audit ( "ERROR: User pressed ESCape during univariate screening" ) ;
            ret_val = ERROR_ESCAPE ;
            goto FINISH ;
            }


/*
   Start a new thread if we still have work to do
*/

         if (ivar < npred) {       // If there are still some to do
            if (empty_slot < 0)    // Negative while we are initially filling the queue
               k = n_threads ;
            else
               k = empty_slot ;
            univar_params[k].ivar = ivar  ;         // Needed for placing final result
            univar_params[k].varnum = preds[ivar] ; // Needed for continuous case
            if (type == SCREEN_UNIVAR_TAILS  ||  type == SCREEN_UNIVAR_DISCRETE) {
               univar_params[k].pred_bin = pred_bin+ivar*n_cases ;
               univar_params[k].pred_marginal = pred_marginal+ivar*nbins_pred ;
               if (type == SCREEN_UNIVAR_TAILS) {
                  univar_params[k].ncases = tail_n[ivar] ;
                  univar_params[k].target_bin = target_bin+ivar*n_cases ;
                  univar_params[k].target_marginal = target_marginal+ivar*nbins_target ;
                  }
               }
            threads[k] = (HANDLE) _beginthreadex ( NULL , 0 , univar_threaded , &univar_params[k] , 0 , NULL ) ;
            if (threads[k] == NULL) {
               audit ( "Internal ERROR: bad thread creation in SCREEN_UNIVAR" ) ;
               for (i=0 ; i<n_threads ; i++) {
                  if (threads[i] != NULL)
                     CloseHandle ( threads[i] ) ;
                  }
               return ERROR_INSUFFICIENT_MEMORY ;
               }
            ++n_threads ;
            ++ivar ;
            } // if (ivar < npred)

         if (n_threads == 0)  // Are we done?
            break ;

/*
   Handle full suite of threads running and more threads to add as soon as some are done.
   Wait for just one thread to finish.
*/

         if (n_threads == max_threads  &&  ivar < npred) {
            ret_val = WaitForMultipleObjects ( n_threads , threads , FALSE , 500000 ) ;
            if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
               sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in SCREEN_UNIVAR", ret_val ) ;
               audit ( msg ) ;
               return ERROR_INSUFFICIENT_MEMORY ;
               }

            crit[univar_params[ret_val].ivar] = univar_params[ret_val].crit ;

            empty_slot = ret_val ;
            CloseHandle ( threads[empty_slot] ) ;
            threads[empty_slot] = NULL ;
            --n_threads ;
            }

/*
   Handle all work has been started and now we are just waiting for threads to finish
*/

         else if (ivar == npred) {
            ret_val = WaitForMultipleObjects ( n_threads , threads , TRUE , 500000 ) ;
            if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
               sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in SCREEN_UNIVAR.CPP", ret_val ) ;
               audit ( msg ) ;
               return ERROR_INSUFFICIENT_MEMORY ;
               }

            for (i=0 ; i<n_threads ; i++) {
               crit[univar_params[i].ivar] = univar_params[i].crit ;
               CloseHandle ( threads[i] ) ;
               }
            break ;
            }
         } // Endless loop which threads computation of criterion for all predictors

/*
   If the user specified 'continuous' then we need to delete the
   MutualInformationAdaptive objects used by each thread.
   This is because the object is based on the target, which is reshuffled each replication.
*/

      if (type == SCREEN_UNIVAR_CONTINUOUS) {
         for (ithread=0 ; ithread<max_threads ; ithread++)
            delete mi_adapt[ithread] ;
         }


/*
   The criterion for each predictor has been computed and saved in crit.
   Update the MCPT.
*/

      for (ivar=0 ; ivar<npred ; ivar++) {

         if (ivar == 0  ||  crit[ivar] > best_crit)
            best_crit = crit[ivar] ;

         if (irep == 0) {            // Original, unpermuted data
            sorted_crits[ivar] = original_crits[ivar] = crit[ivar] ;
            index[ivar] = ivar ;
            mcpt_bestof[ivar] = mcpt_solo[ivar] = 1 ;
            }

         else if (crit[ivar] >= original_crits[ivar])
            ++mcpt_solo[ivar] ;

         } // For all predictor candidates


      if (irep == 0)   // Get the indices that sort the predictors' mutual information
         qsortdsi ( 0 , npred-1 , sorted_crits , index ) ;

      else {
         for (ivar=0 ; ivar<npred ; ivar++) {
            if (best_crit >= original_crits[ivar]) // Valid only for largest
               ++mcpt_bestof[ivar] ;
            }
         }

      } // For all MCPT replications


/*
--------------------------------------------------------------------------------

   All main computation is finished.  Print results.

--------------------------------------------------------------------------------
*/

   audit ( "" ) ;
   audit ( "" ) ;
   if (type == SCREEN_UNIVAR_CONTINUOUS) {
      if (subtype == SCREEN_UNIVAR_CMI)
         sprintf_s ( msg, "-------------------> Continuous mutual Information with %s <-----------------", var_names[targetvar] ) ;
      else if (subtype == SCREEN_UNIVAR_R)
         sprintf_s ( msg, "------------------------------> Pearson's r with %s <------------------------------", var_names[targetvar] ) ;
      else if (subtype == SCREEN_UNIVAR_RHO)
         sprintf_s ( msg, "------------------------------> Spearman rho with %s <------------------------------", var_names[targetvar] ) ;
      else if (subtype == SCREEN_UNIVAR_QUAD)
         sprintf_s ( msg, "------------------------------> Quadratic R-squared with %s <------------------------------", var_names[targetvar] ) ;
      }
   else if (type == SCREEN_UNIVAR_TAILS  ||  type == SCREEN_UNIVAR_DISCRETE) {
      if (subtype == SCREEN_UNIVAR_DMI)
         sprintf_s ( msg, "--------------------------> Discrete mutual Information with %s <--------------------------", var_names[targetvar] ) ;
      else if (subtype == SCREEN_UNIVAR_UNCERT)
         sprintf_s ( msg, "------------------------------> Uncertainty reduction with %s <------------------------------", var_names[targetvar] ) ;
      else if (subtype == SCREEN_UNIVAR_V)
         sprintf_s ( msg, "------------------------------> Cramer's V with %s <------------------------------", var_names[targetvar] ) ;
      }
   audit ( msg ) ;

   audit ( "" ) ;
   audit ( "" ) ;
   if (type == SCREEN_UNIVAR_CONTINUOUS) {
      if (subtype == SCREEN_UNIVAR_CMI)
         strcpy_s ( msg , "       Variable        MutInf   " ) ;
      else if (subtype == SCREEN_UNIVAR_R)
         strcpy_s ( msg , "       Variable     Pearson's r " ) ;
      else if (subtype == SCREEN_UNIVAR_RHO)
         strcpy_s ( msg , "       Variable    Spearman rho " ) ;
      else if (subtype == SCREEN_UNIVAR_QUAD)
         strcpy_s ( msg , "       Variable    Quadratic Rsq" ) ;
      }
   else if (type == SCREEN_UNIVAR_TAILS  ||  type == SCREEN_UNIVAR_DISCRETE) {
      if (subtype == SCREEN_UNIVAR_DMI)
         strcpy_s ( msg , "       Variable        MutInf   " ) ;
      else if (subtype == SCREEN_UNIVAR_UNCERT)
         strcpy_s ( msg , "       Variable    UncertReduc   " ) ;
      else if (subtype == SCREEN_UNIVAR_V)
         strcpy_s ( msg , "       Variable     Cramer's V   " ) ;
      }

   if (mcpt_reps > 1)
      strcat_s ( msg, "  Solo pval  Unbiased pval" ) ;
   if (half_S)
      strcat_s ( msg, "     P(<=median)" ) ;
   audit ( msg ) ;
   audit ( "" ) ;

   for (i=npred-1 ; i>=0 ; i--) {
      k = index[i] ;
      sprintf_s ( msg, "%15s  %12.4lf",
                var_names[preds[k]], original_crits[k] ) ;
      if (mcpt_reps > 1) {
         sprintf_s ( msg2, " %12.4lf %12.4lf",
                   (double) mcpt_solo[k] / (double) mcpt_reps,
                   (double) mcpt_bestof[k] / (double) mcpt_reps ) ;
         strcat_s ( msg , msg2 ) ;
         }
      if (half_S) {
         sprintf_s ( msg2, "     %12.4lf", cscv_crits[i] ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;
      }

/*
   Finished.  Clean up and exit.
*/

FINISH:
   if (pred != NULL)
      free ( pred ) ;
   if (crit != NULL)
      free ( crit ) ;
   if (index != NULL)
      free ( index ) ;
   if (pred_thresholds != NULL)
      free ( pred_thresholds ) ;
   if (target_thresholds != NULL)
      free ( target_thresholds ) ;
   if (target_bin != NULL)
      free ( target_bin ) ;
   if (pred_bin != NULL)
      free ( pred_bin ) ;
   if (work_bin != NULL)
      free ( work_bin ) ;
   if (bin_counts != NULL)
      free ( bin_counts ) ;
   if (work1 != NULL)
      free ( work1 ) ;
   if (work2 != NULL)
      free ( work2 ) ;

   if (cscv_crits != NULL)
      free ( cscv_crits ) ;
   if (cscv_indices != NULL)
      free ( cscv_indices ) ;
   if (cscv_indep != NULL)
      free ( cscv_indep ) ;
   if (cscv_work_pred != NULL)
      free ( cscv_work_pred ) ;
   if (cscv_iwork_pred != NULL)
      free ( cscv_iwork_pred ) ;

   for (i=0 ; i<max_threads ; i++) {
      if (sptr[i] != NULL)
         delete sptr[i] ;
      }

   return ret_val ;
}