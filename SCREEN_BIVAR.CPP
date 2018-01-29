/******************************************************************************/
/*                                                                            */
/*  SCREEN_BIVAR - Mutual information between two predictors and a target     */
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
--------------------------------------------------------------------------------

   Subroutine to compute discrete mutual information

--------------------------------------------------------------------------------
*/

static double compute_mi (
   int ncases ,                 // Number of cases
   int nbins_pred ,             // Number of predictor bins
   int *pred1_bin ,             // Ncases vector of predictor 1 bin indices
   int *pred2_bin ,             // Ncases vector of predictor 2 bin indices
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices
   double *target_marginal ,    // Target marginal
   int *bin_counts              // Work area nbins_pred_squared*nbins_target long
   )
{
   int i, j, k, nbins_pred_squared ;
   double px, py, pxy, MI ;

   // Zero all bin counts

   nbins_pred_squared = nbins_pred * nbins_pred ;

   for (i=0 ; i<nbins_pred_squared ; i++) {
      for (j=0 ; j<nbins_target ; j++)
         bin_counts[i*nbins_target+j] = 0 ;
      }


   // Compute bin counts for bivariate predictor and full table

   for (i=0 ; i<ncases ; i++) {
      k = pred1_bin[i]*nbins_pred+pred2_bin[i] ;
      ++bin_counts[k*nbins_target+target_bin[i]] ;
      }

   // Compute mutual information

   MI = 0.0 ;
   for (i=0 ; i<nbins_pred_squared ; i++) {
      k = 0 ;
      for (j=0 ; j<nbins_target ; j++)  // Sum across target bins to get predictor marginal
         k += bin_counts[i*nbins_target+j] ;
      px = (double) k / (double) ncases ;

      for (j=0 ; j<nbins_target ; j++) {
         py = target_marginal[j] ;
         pxy = (double) bin_counts[i*nbins_target+j] / (double) ncases ;
         if (pxy > 0.0)
            MI += pxy * log ( pxy / (px * py) ) ;
         }
      }

   if (nbins_pred_squared <= nbins_target)
      MI /= log ( (double) nbins_pred_squared ) ;  // Normalize 0-1
   else
      MI /= log ( (double) nbins_target ) ;

   return MI ;
}


/*
--------------------------------------------------------------------------------

   uncert_reduc - Uncertainty reduction for a pair of indicators and a target

--------------------------------------------------------------------------------
*/

void uncert_reduc (
   int ncases ,               // Number of cases
   int nbins_pred ,           // Number of predictor bins
   int *pred1_bin ,           // Ncases vector of predictor 1 bin indices
   int *pred2_bin ,           // Ncases vector of predictor 2 bin indices
   int nbins_target ,         // Number of target bins
   int *target_bin ,          // Ncases vector of target bin indices
   double *target_marginal ,  // Target marginal
   double *row_dep,           // Returns asymmetric UR when row is dependent
   double *col_dep,           // Returns asymmetric UR when column is dependent
   double *sym,               // Returns symmetric UR
   int *rmarg,                // Work vector nbins_pred_squared long
   int *bin_counts            // Work area nbins_pred*nbins_target long
   )
{
   int i, j, k, irow, icol, total, nbins_pred_squared ;
   double p, numer, Urow, Ucol, Ujoint ;

   // Zero all bin counts

   nbins_pred_squared = nbins_pred * nbins_pred ;

   for (i=0 ; i<nbins_pred_squared ; i++) {
      for (j=0 ; j<nbins_target ; j++)
         bin_counts[i*nbins_target+j] = 0 ;
      }


   // Compute bin counts for bivariate predictor and full table

   for (i=0 ; i<ncases ; i++) {
      k = pred1_bin[i]*nbins_pred+pred2_bin[i] ;
      ++bin_counts[k*nbins_target+target_bin[i]] ;
      }

   total = 0 ;

   for (irow=0 ; irow<nbins_pred_squared ; irow++) {
      rmarg[irow] = 0 ;
      for (icol=0 ; icol<nbins_target ; icol++)
         rmarg[irow] += bin_counts[irow*nbins_target+icol] ;
      total += rmarg[irow] ;
      }

   // Compute intermediate quantities

   Urow = 0.0 ;
   for (irow=0 ; irow<nbins_pred_squared ; irow++) {
      if (rmarg[irow]) {
         p = (double) rmarg[irow] / (double) total ;
         Urow -= p * log ( p ) ;
         }
      }

   Ucol = 0.0 ;
   for (icol=0 ; icol<nbins_target ; icol++) {
      if (target_marginal[icol] > 0.0) {
         p = target_marginal[icol] ;
         Ucol -= p * log ( p ) ;
         }
      }

   Ujoint = 0.0 ;
   for (irow=0 ; irow<nbins_pred_squared ; irow++) {
      for (icol=0 ; icol<nbins_target ; icol++) {
         if (bin_counts[irow*nbins_target+icol]) {
            p = (double) bin_counts[irow*nbins_target+icol] / (double) total ;
            Ujoint -= p * log ( p ) ;
            }
         }
      }

   numer = Urow + Ucol - Ujoint ;
   if (Urow > 0.0)
      *row_dep = numer / Urow ;
   else
      *row_dep = 0.0 ;
   if (Ucol > 0.0)
      *col_dep = numer / Ucol ;
   else
      *col_dep = 0.0 ;
   if (Urow + Ucol > 0.0)
      *sym = 2.0 * numer / (Urow + Ucol) ;
   else
      *sym = 0.0 ;
}   


/*
--------------------------------------------------------------------------------

   Thread stuff...  Structure for passing information to/from threaded code
                    called by the main subroutine

--------------------------------------------------------------------------------
*/

typedef struct {
   int icombo ;              // Index of predictor/target combination needed for placing crit
   int ncases ;              // Number of cases
   int nbins_pred ;          // Number of predictor bins
   int nbins_target ;        // Number of target bins
   int which ;               // 1=mutual information, 2=uncertainty reduction
   double crit ;             // Criterion is returned here
   int *bin_counts ;         // Work area for complete bin counting
   int *bivar_counts ;       // Work area for bivariate predictor bin counting
   int *pred1_bin ;          // Bin index for predictor 1
   int *pred2_bin ;          // Bin index for predictor 2
   int *target_bin ;         // Bin index for targets
   double *target_marginal ; // Marginal density of target
} BIVAR_PARAMS ;

static unsigned int __stdcall bivar_threaded_wrapper ( LPVOID dp )
{
   double crit, dummy1, dummy2 ;

   if (((BIVAR_PARAMS *) dp)->which == 1)
      crit = compute_mi ( ((BIVAR_PARAMS *) dp)->ncases ,
                          ((BIVAR_PARAMS *) dp)->nbins_pred ,
                          ((BIVAR_PARAMS *) dp)->pred1_bin ,
                          ((BIVAR_PARAMS *) dp)->pred2_bin ,
                          ((BIVAR_PARAMS *) dp)->nbins_target ,
                          ((BIVAR_PARAMS *) dp)->target_bin ,
                          ((BIVAR_PARAMS *) dp)->target_marginal ,
                          ((BIVAR_PARAMS *) dp)->bin_counts ) ;

   else
      uncert_reduc ( ((BIVAR_PARAMS *) dp)->ncases ,
                     ((BIVAR_PARAMS *) dp)->nbins_pred ,
                     ((BIVAR_PARAMS *) dp)->pred1_bin ,
                     ((BIVAR_PARAMS *) dp)->pred2_bin ,
                     ((BIVAR_PARAMS *) dp)->nbins_target ,
                     ((BIVAR_PARAMS *) dp)->target_bin ,
                     ((BIVAR_PARAMS *) dp)->target_marginal ,
                     &dummy1 , &crit , &dummy2 ,
                     ((BIVAR_PARAMS *) dp)->bivar_counts ,
                     ((BIVAR_PARAMS *) dp)->bin_counts ) ;

   ((BIVAR_PARAMS *) dp)->crit = crit ;
   return 0 ;
}


/*
--------------------------------------------------------------------------------

   Local subroutine uses CPU threading to do a replication

   NOTE ON THREADS... If the thread workload is low, overhead will keep CPU time
                      low.  If debug printing, one will see that only the first
                      thread keeps ending and getting replaced.  Threading behaves
                      as expected only when each thread uses a lot of CPU time.

--------------------------------------------------------------------------------
*/

static int bivar_threaded (
   int mcpt_reps ,              // Only for knowing whether to update progress bar
   int max_threads ,            // Maximum number of threads to use
   int ncases ,                 // Number of cases
   int npred ,                  // Number of predictor candidates
   int ntarget ,                // Number of target candidates
   int nbins_pred ,             // Number of predictor bins
   int *pred_bin ,              // Ncases vector of predictor bin indices, npred of them
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices, ntarget of them
   double *target_marginal ,    // Target marginal, ntarget of them
   int which ,                  // 1=mutual information, 2=uncertainty reduction
   double *crit ,               // Output of all criteria, npred * (npred-1) / 2 * ntarget long
   int *bin_counts ,            // Work area max_threads*nbins_pred*nbins_pred*nbins_target long
   int *bivar_counts            // Work area max_threads*nbins_pred_squared long
   )
{
   int i, k, ret_val, ithread, n_threads, empty_slot ;
   int ipred1, ipred2, itarget, icombo, n_combo ;
   char msg[4096] ;
   BIVAR_PARAMS bivar_params[MAX_THREADS] ;
   HANDLE threads[MAX_THREADS] ;

/*
   Initialize those thread parameters which are constant for all threads.
   Each thread will have its own private bin_count and bivar_count matrices for working storage.
*/

   for (ithread=0 ; ithread<max_threads ; ithread++) {
      bivar_params[ithread].ncases = n_cases ;
      bivar_params[ithread].nbins_pred = nbins_pred ;
      bivar_params[ithread].nbins_target = nbins_target ;
      bivar_params[ithread].bin_counts = bin_counts + ithread * nbins_pred * nbins_pred * nbins_target ;
      bivar_params[ithread].bivar_counts = bivar_counts + ithread * nbins_pred * nbins_pred ;
      bivar_params[ithread].which = which ;
      } // For all threads, initializing constant stuff


/*
   Do it
   We use icombo to define a unique set of two predictors and one target.
   It ranges from 0 through npred * (npred-1) / 2 * ntarget.
*/

   n_threads = 0 ;                    // Counts threads that are active
   for (i=0 ; i<max_threads ; i++)
      threads[i] = NULL ;


   ipred1 = itarget = icombo = 0 ;
   ipred2 = 1 ;
   n_combo = npred * (npred-1) / 2 * ntarget ;  // This many combinations

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
         return ERROR_ESCAPE ;
         }


/*
   Start a new thread if we still have work to do
*/

      if (icombo < n_combo) {   // If there are still some to do
         if (empty_slot < 0)    // Negative while we are initially filling the queue
            k = n_threads ;
         else
            k = empty_slot ;
         bivar_params[k].icombo = icombo  ;   // Needed for placing final result
         bivar_params[k].pred1_bin = pred_bin+ipred1*ncases ;
         bivar_params[k].pred2_bin = pred_bin+ipred2*ncases ;
         bivar_params[k].target_bin = target_bin+itarget*ncases ;
         bivar_params[k].target_marginal = target_marginal+itarget*nbins_target ;
         threads[k] = (HANDLE) _beginthreadex ( NULL , 0 , bivar_threaded_wrapper , &bivar_params[k] , 0 , NULL ) ;
         if (threads[k] == NULL) {
            audit ( "Internal ERROR: bad thread creation in SCREEN_BIVAR" ) ;
            for (i=0 ; i<n_threads ; i++) {
               if (threads[i] != NULL)
                  CloseHandle ( threads[i] ) ;
               }
            return ERROR_INSUFFICIENT_MEMORY ;
            }
         ++n_threads ;

         // Advance to the next combination

         ++icombo ;
         if (itarget < ntarget-1)
            ++itarget ;
         else {
            itarget = 0 ;
            if (ipred2 < npred-1)
              ++ipred2 ;
            else {
               ++ipred1 ;
               ipred2 = ipred1 + 1 ;
               }
            }

         } // if (icombo < n_combo)

      if (n_threads == 0)  // Are we done?
         break ;

/*
   Handle full suite of threads running and more threads to add as soon as some are done.
   Wait for just one thread to finish.
*/

      if (n_threads == max_threads  &&  icombo < n_combo) {
         ret_val = WaitForMultipleObjects ( n_threads , threads , FALSE , 500000 ) ;
         if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
            sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in SCREEN_BIVAR", ret_val ) ;
            audit ( msg ) ;
            return ERROR_INSUFFICIENT_MEMORY ;
            }

         crit[bivar_params[ret_val].icombo] = bivar_params[ret_val].crit ;

         if (mcpt_reps == 1) {
            sprintf_s ( msg , "Combination %d of %d", icombo+1, n_combo ) ;
            title_progbar ( msg ) ;
            setpos_progbar ( (double) (icombo+1) / (double) n_combo ) ;
            }

         empty_slot = ret_val ;
         CloseHandle ( threads[empty_slot] ) ;
         threads[empty_slot] = NULL ;
         --n_threads ;
         }

/*
   Handle all work has been started and now we are just waiting for threads to finish
*/

      else if (icombo == n_combo) {
         ret_val = WaitForMultipleObjects ( n_threads , threads , TRUE , 500000 ) ;
         if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
            sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in SCREEN_BIVAR.CPP", ret_val ) ;
            audit ( msg ) ;
            return ERROR_INSUFFICIENT_MEMORY ;
            }

         for (i=0 ; i<n_threads ; i++) {
            crit[bivar_params[i].icombo] = bivar_params[i].crit ;
            CloseHandle ( threads[i] ) ;
            }
         break ;
         }
      } // Endless loop which threads computation of criterion for all predictors

   return 0 ;
}

/*
--------------------------------------------------------------------------------

   Main subroutine to compute and print bivariate mutual information study

--------------------------------------------------------------------------------
*/

int screen_bivar (
   int npred ,        // Number of predictors
   int *preds ,       // Their indices are here
   int ntarget ,      // Number of targets
   int *targets ,     // Their indices are here
   int nbins_pred ,   // Number of predictor bins
   int nbins_target , // Number of target bins, 0 for 2 sign-based bins
   int which ,        // 1=mutual_information, 2=uncertainty reduction
   int mcpt_type ,    // 1=complete, 2=cyclic
   int mcpt_reps ,    // Number of MCPT replications, <=1 for no MCPT
   int max_printed    // Max number of combinations to print
   )
{
   int i, j, k, ret_val, ivar, irep, varnum, max_threads ;
   int *index, *mcpt_solo, *mcpt_bestof, *pred_bin, *target_bin, *bin_counts, *bivar_counts ;
   int ipred1, ipred2, itarget, icombo, n_combo, *work_bin ;
   double *casework, *sorted, *mutual, *pred_thresholds, *target_thresholds ;
   double *crit, *original_crits, *sorted_crits, best_crit ;
   double *pred_bounds, *target_bounds, *pred_marginal, *target_marginal ;
   char msg[4096], msg2[4096] ;

   casework = NULL ;
   mutual = NULL ;
   index = NULL ;
   pred_thresholds = NULL ;
   target_thresholds = NULL ;
   pred_bin = NULL ;
   bin_counts = NULL ;
   bivar_counts = NULL ;

   ret_val = 0 ;

   max_threads = MAX_THREADS ;

/*
   Print header
*/

   n_combo = npred * (npred-1) / 2 * ntarget ;  // This many combinations

   audit ( "" ) ;
   audit ( "" ) ;
   audit ( "******************************************************************************" ) ;
   audit ( "*                                                                            *" ) ;
   if (which == 1)
      audit ( "* Computing bivariate mutual information (two predictors, one target)        *" ) ;
   else
      audit ( "* Computing bivariate uncertainty reduction (two predictors, one target)     *" ) ;
   sprintf_s ( msg, "*   %5d predictor candidates                                               *", npred ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "*   %5d target candidates                                                  *", ntarget ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "* %7d predictor/target combinations to test                              *", n_combo ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "* %7d best combinations will be printed                                  *", max_printed ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "*      %2d predictor bins                                                     *", nbins_pred ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "*      %2d target bins                                                        *", nbins_target ) ;
   audit ( msg ) ;
   if (mcpt_reps > 1) {
      if (mcpt_type == 1)
         sprintf_s ( msg, "*   %5d replications of complete Monte-Carlo Permutation Test              *", mcpt_reps ) ;
      else if (mcpt_type == 2)
         sprintf_s ( msg, "*   %5d replications of cyclic Monte-Carlo Permutation Test                *", mcpt_reps ) ;
      audit ( msg ) ;
      }
   else {
      sprintf_s ( msg, "*         No Monte-Carlo Permutation Test                                    *" ) ;
      audit ( msg ) ;
      }
   audit ( "*                                                                            *" ) ;
   audit ( "******************************************************************************" ) ;

   if (n_combo > 100000) {
      audit ( "ERROR: BIVARIATE SCREENING can have at most 100,000 combinations" ) ;
      ret_val = ERROR_INSUFFICIENT_MEMORY ;
      goto FINISH ;
      }


/*
   Allocate memory
*/

   casework = (double *) malloc ( 2 * n_cases * sizeof(double) ) ;  // Pred, sorted
   sorted = casework + n_cases ;

   mutual = (double *) malloc ( 4 * n_combo * sizeof(double) ) ;  // Mutual, crit, original_crits, sorted_crits
   crit = mutual + n_combo ;
   original_crits = crit + n_combo ;
   sorted_crits = original_crits + n_combo ;

   index = (int *) malloc ( 3 * n_combo * sizeof(int) ) ;   // Index, mcpt_solo, mcpt_bestof
   mcpt_solo = index + n_combo ;
   mcpt_bestof = mcpt_solo + n_combo ;

   pred_thresholds = (double *) malloc ( 2 * nbins_pred * npred * sizeof(double) ) ; // pred_thresholds, pred_marginal
   pred_marginal = pred_thresholds + npred * nbins_pred ; // Not needed for computation but nice to print for user

   target_thresholds = (double *) malloc ( 2 * ntarget * nbins_target * sizeof(double) ) ; // target_thresholds, target_marginal
   target_marginal = target_thresholds + ntarget * nbins_target ;

   pred_bin = (int *) malloc ( (npred+ntarget+1) * n_cases * sizeof(int) ) ; // Pred_bin, target_bin, work_bin
   target_bin = pred_bin + npred * n_cases ;
   work_bin = target_bin + ntarget * n_cases ;

   bin_counts = (int *) malloc ( max_threads * nbins_pred * nbins_pred * nbins_target * sizeof(int) ) ;
   bivar_counts = (int *) malloc ( max_threads * nbins_pred * nbins_pred * sizeof(int) ) ;

   if (casework == NULL  ||  mutual == NULL  ||  index == NULL  ||
       pred_thresholds == NULL  ||  target_thresholds == NULL  ||
       pred_bin == NULL  ||  bin_counts == NULL  ||  bivar_counts == NULL) {
      audit ( "ERROR: Insufficient memory for MUTUAL INFORMATION" ) ;
      ret_val = ERROR_INSUFFICIENT_MEMORY ;
      goto FINISH ;
      }

/*
   Make an initial pass through the data to find all thresholds and
   permanently save bin indices for predictors and target.
*/

   for (ivar=0 ; ivar<npred+ntarget ; ivar++) {

      if (ivar < npred) {
         varnum = preds[ivar] ;
         pred_bounds = pred_thresholds + ivar * nbins_pred ;
         }
      else {
         varnum = targets[ivar-npred] ;
         target_bounds = target_thresholds + (ivar-npred) * nbins_target ;
         }

      if (user_pressed_escape()) {
         audit ( "ERROR: User pressed ESCape during MUTUAL INFORMATION" ) ;
         ret_val = ERROR_ESCAPE ;
         goto FINISH ;
         }

      for (i=0 ; i<n_cases ; i++)               // Extract predictor or target from database
         casework[i] = database[i*n_vars+varnum] ;

      if (ivar < npred) {
         k = nbins_pred ;
         partition ( n_cases , casework , &k , pred_bounds , pred_bin+ivar*n_cases ) ;
         if (k <nbins_pred) {
            sprintf_s ( msg, "ERROR: Numerous ties reduced predictor %s bins to %d", var_names[preds[ivar]], k ) ;
            audit ( msg ) ;
            ret_val = ERROR_SYNTAX ;
            goto FINISH ;
            }
         assert ( k == nbins_pred ) ;
         }
      else {
         k = nbins_target ;
         partition ( n_cases , casework , &k , target_bounds , target_bin+(ivar-npred)*n_cases ) ;
         if (k <nbins_target) {
            sprintf_s ( msg, "ERROR: Numerous ties reduced target %s bins to %d", var_names[targets[ivar]], k ) ;
            audit ( msg ) ;
            ret_val = ERROR_SYNTAX ;
            goto FINISH ;
            }
         assert ( k == nbins_target ) ;
         }

      } // For ivar (reading each variable, npred+ntarget of them)


/*
   All thresholds (predictor and target) are computed and saved.
   The predictor and target bin indices are also saved.

   Print the thresholds for the user's edification
*/

   audit ( "" ) ;
   audit ( "" ) ;
   audit ( "The bounds that define bins are now shown" ) ;
   audit ( "" ) ;

   for (ivar=0 ; ivar<npred ; ivar++) {
      pred_bounds = pred_thresholds + ivar * nbins_pred ;
      sprintf_s ( msg, "%15s  %12.5lf", var_names[preds[ivar]], pred_bounds[0] ) ;
      for (i=1 ; i<nbins_pred-1 ; i++) {
         sprintf_s ( msg2 , "  %12.5lf", pred_bounds[i] ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;
      } // For all predictors

   audit ( "" ) ;
   for (ivar=0 ; ivar<ntarget ; ivar++) {
      target_bounds = target_thresholds + ivar * nbins_target ;
      sprintf_s ( msg, "%15s  %12.5lf", var_names[targets[ivar]], target_bounds[0] ) ;
      for (i=1 ; i<nbins_target-1 ; i++) {
         sprintf_s ( msg2 , "  %12.5lf", target_bounds[i] ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;
      } // For all targets

/*
   Compute marginals
*/

   for (ivar=0 ; ivar<npred ; ivar++) {
      for (i=0 ; i<nbins_pred ; i++)
         pred_marginal[ivar*nbins_pred+i] = 0.0 ;
      for (i=0 ; i<n_cases ; i++)
         ++pred_marginal[ivar*nbins_pred+pred_bin[ivar*n_cases+i]] ;
      }

   for (ivar=0 ; ivar<npred ; ivar++) {  // Divide counts by number of cases to get marginal
      for (i=0 ; i<nbins_pred ; i++)
         pred_marginal[ivar*nbins_pred+i] /= n_cases ;
      }

   for (ivar=0 ; ivar<ntarget ; ivar++) {
      for (i=0 ; i<nbins_target ; i++)
         target_marginal[ivar*nbins_target+i] = 0.0 ;
      for (i=0 ; i<n_cases ; i++)
         ++target_marginal[ivar*nbins_target+target_bin[ivar*n_cases+i]] ;
      }

   for (ivar=0 ; ivar<ntarget ; ivar++) {  // Divide counts by number of cases to get marginal
      for (i=0 ; i<nbins_target ; i++)
         target_marginal[ivar*nbins_target+i] /= n_cases ;
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

   for (ivar=0 ; ivar<npred ; ivar++) {
      sprintf_s ( msg, "%15s  %12.5lf", var_names[preds[ivar]], pred_marginal[ivar*nbins_pred+0] ) ;
      for (i=1 ; i<nbins_pred ; i++) {
         sprintf_s ( msg2 , "  %12.5lf", pred_marginal[ivar*nbins_pred+i] ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;
      } // For all predictors

   audit ( "" ) ;
   for (ivar=0 ; ivar<ntarget ; ivar++) {
      sprintf_s ( msg, "%15s  %12.5lf", var_names[targets[ivar]], target_marginal[ivar*nbins_target+0] ) ;
      for (i=1 ; i<nbins_target ; i++) {
         sprintf_s ( msg2 , "  %12.5lf", target_marginal[ivar*nbins_target+i] ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;
      } // For all targets



/*
--------------------------------------------------------------------------------

   Outer-most loop does MCPT replications

--------------------------------------------------------------------------------
*/

   if (mcpt_reps < 1)
      mcpt_reps = 1 ;

   for (irep=0 ; irep<mcpt_reps ; irep++) {
         
/*
   Shuffle target(s) if in permutation run (irep>0)
   This needs to be done BEFORE the main 'compute MI of each predictor/target'
   loop because the logic of shuffling just once at the start of each
   replication would be excessivly complex with threading.
*/

      if (irep) {                  // If doing permuted runs, shuffle

         if (mcpt_type == 1) {     // Complete
            i = n_cases ;          // Number remaining to be shuffled
            while (i > 1) {        // While at least 2 left to shuffle
               j = (int) (unifrand_fast () * i) ;
               if (j >= i)
                  j = i - 1 ;
               --i ;
               for (ivar=0 ; ivar<ntarget ; ivar++) {
                  k = target_bin[ivar*n_cases+i] ;
                  target_bin[ivar*n_cases+i] = target_bin[ivar*n_cases+j] ;
                  target_bin[ivar*n_cases+j] = k ;
                  }
               }
            } // Type 1, complete

         else if (mcpt_type == 2) { // Cyclic
            j = (int) (unifrand_fast () * n_cases) ;
            if (j >= n_cases)
               j = n_cases - 1 ;
            for (ivar=0 ; ivar<ntarget ; ivar++) {
               for (i=0 ; i<n_cases ; i++)
                  work_bin[i] = target_bin[ivar*n_cases+(i+j)%n_cases] ;
               for (i=0 ; i<n_cases ; i++)
                  target_bin[ivar*n_cases+i] = work_bin[i]  ;
               }
            } // Type 2, cyclic

         } // If in permutation run (irep > 0)


/*
-----------------------------------------------------------------------------------

   Compute and save criterion for all combinations.

-----------------------------------------------------------------------------------
*/

      ret_val = bivar_threaded ( mcpt_reps , max_threads , n_cases , npred , ntarget ,
                               nbins_pred , pred_bin , nbins_target , target_bin ,
                               target_marginal , which , crit , bin_counts , bivar_counts ) ;

      if (user_pressed_escape()  &&  ret_val == 0)
         ret_val = ERROR_ESCAPE ;

      if (ret_val) {
         audit ( "ERROR: User pressed ESCape during MUTUAL INFORMATION" ) ;
         goto FINISH ;
         }

      if (mcpt_reps > 1) {
         sprintf_s ( msg , "Replication %d of %d", irep+1, mcpt_reps ) ;
         title_progbar ( msg ) ;
         setpos_progbar ( (double) (irep+1) / (double) mcpt_reps ) ;
         }

/*
   The criterion for each predictor has been computed and saved in crit.
   Update the MCPT.
*/

      for (icombo=0 ; icombo<n_combo ; icombo++) {

         if (icombo == 0  ||  crit[icombo] > best_crit)
            best_crit = crit[icombo] ;

         if (irep == 0) {            // Original, unpermuted data
            sorted_crits[icombo] = original_crits[icombo] = crit[icombo] ;
            index[icombo] = icombo ;
            mcpt_bestof[icombo] = mcpt_solo[icombo] = 1 ;
            }

         else if (crit[icombo] >= original_crits[icombo])
            ++mcpt_solo[icombo] ;

         } // For all predictor candidates


      if (irep == 0)   // Get the indices that sort the predictors' mutual information
         qsortdsi ( 0 , n_combo-1 , sorted_crits , index ) ;

      else {
         for (icombo=0 ; icombo<n_combo ; icombo++) {
            if (best_crit >= original_crits[icombo]) // Valid only for largest
               ++mcpt_bestof[icombo] ;
            }
         }

      } // For all MCPT replications


/*
--------------------------------------------------------------------------------

   All computation is finished.  Print.

--------------------------------------------------------------------------------
*/

   audit ( "" ) ;
   audit ( "" ) ;
   if (which == 1)
      audit ( "------------------------------> Mutual Information <------------------------------" ) ;
   else
      audit ( "-----------------------------> Uncertainty reduction <------------------------------" ) ;
   audit ( "" ) ;

   if (mcpt_reps > 1) {
      if (which == 1)
         audit ( "    Predictor 1     Predictor 2          Target         MI      Solo pval  Unbiased pval" ) ;
      else
         audit ( "    Predictor 1     Predictor 2          Target         UR      Solo pval  Unbiased pval" ) ;
      }
   else {
      if (which == 1)
         audit ( "    Predictor 1     Predictor 2          Target         MI" ) ;
      else
         audit ( "    Predictor 1     Predictor 2          Target         UR" ) ;
      }
   audit ( "" ) ;

   for (i=n_combo-1 ; i>=0 ; i--) {

      if (max_printed-- <= 0)
         break ;

      k = index[i] ;
      assert ( k >= 0  &&  k < n_combo ) ;

      // This is a ridiculously crude way to get the predictors and target from the combo.
      // There must be a formula.  But this adds negligible time, so be lazy.

      ipred1 = itarget = icombo = 0 ;
      ipred2 = 1 ;
      while (icombo < n_combo) {
         if (icombo == k)
            break ;
         ++icombo ;
         if (itarget < ntarget-1)
            ++itarget ;
         else {
            itarget = 0 ;
            if (ipred2 < npred-1)
              ++ipred2 ;
            else {
               ++ipred1 ;
               ipred2 = ipred1 + 1 ;
               }
            }
         }

      sprintf_s ( msg, "%15s %15s %15s %12.4lf",
                 var_names[preds[ipred1]], var_names[preds[ipred2]], var_names[targets[itarget]],
                 original_crits[k] ) ;
      if (mcpt_reps > 1) {
         sprintf_s ( msg2, " %12.4lf %12.4lf",
                     (double) mcpt_solo[k] / (double) mcpt_reps,
                     (double) mcpt_bestof[k] / (double) mcpt_reps ) ;
         strcat_s ( msg , msg2 ) ;
         }
      audit ( msg ) ;

      }

/*
   Finished.  Clean up and exit.
*/

FINISH:

   if (casework != NULL)
      free ( casework ) ;
   if (mutual != NULL)
      free ( mutual ) ;
   if (index != NULL)
      free ( index ) ;
   if (pred_thresholds != NULL)
      free ( pred_thresholds ) ;
   if (target_thresholds != NULL)
      free ( target_thresholds ) ;
   if (pred_bin != NULL)
      free ( pred_bin ) ;
   if (bin_counts != NULL)
      free ( bin_counts ) ;
   if (bivar_counts != NULL)
      free ( bivar_counts ) ;
   return ret_val ;
}
