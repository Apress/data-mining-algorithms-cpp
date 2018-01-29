/*********************************************************************************/
/*                                                                               */
/*  RR - Relevance minus redundancy for building an optimal subset of predictors */
/*                                                                               */
/*  The 'tails' option is not strictly correct because it does trinary MI        */
/*                                                                               */
/*********************************************************************************/

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

   Subroutine to compute NORMALIZED discrete mutual information

--------------------------------------------------------------------------------
*/

static double compute_mi (
   int ncases ,                 // Number of cases
   int nbins_pred ,             // Number of predictor bins
   int *pred_bin ,              // Ncases vector of predictor bin indices
   double *pred_marginal ,      // Predictor marginal
   int nbins_target ,           // Number of target bins
   int *target_bin ,            // Ncases vector of target bin indices
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

   if (nbins_pred <= nbins_target)
      MI /= log ( (double) nbins_pred ) ;
   else
      MI /= log ( (double) nbins_target ) ;

   return MI ;
}


/*
--------------------------------------------------------------------------------

   Thread stuff...  Structure for passing information to/from threaded code
                    called by the main subroutine

--------------------------------------------------------------------------------
*/

typedef struct {
   int type ;                // Type of study (SCREEN_RR_? in CONST.H): continuous, tails, discrete)
   int ix ;                  // Index of predictor (in which_preds, not database)
   int ncases ;              // Number of cases
   int nbins_X ;             // Number of predictor bins
   int *X_bin ;              // Bin index for predictors
   double *X_marginal ;      // Marginal density of predictor
   int nbins_Y ;             // Number of target bins
   int *Y_bin ;              // Bin index for targets
   double *Y_marginal ;      // Marginal density of target
   double crit ;             // Criterion is returned here
   int *bin_counts ;         // Work area for bin counting
   MutualInformationAdaptive *mi_adapt ;  // Used for CONTINUOUS only
   double *database ;        // Full database (this and next two lines used for continuous methods only)
   int n_vars ;              // Number of columns in database
   int varnum ;              // Index of predictor (in database, not preds)
} RR_PARAMS ;

static unsigned int __stdcall mutinf_threaded ( LPVOID dp )
{
   double crit ;
   MutualInformationAdaptive *mi_adapt ;

   if (((RR_PARAMS *) dp)->type == SCREEN_RR_CONTINUOUS) {
      mi_adapt = ((RR_PARAMS *) dp)->mi_adapt ;
      crit = mi_adapt->compute_mut_inf ( ((RR_PARAMS *) dp)->database , 1 ,
                                         ((RR_PARAMS *) dp)->varnum ,
                                         ((RR_PARAMS *) dp)->n_vars ) ;
      }

   else {
      crit = compute_mi ( ((RR_PARAMS *) dp)->ncases ,
                          ((RR_PARAMS *) dp)->nbins_X ,
                          ((RR_PARAMS *) dp)->X_bin ,
                          ((RR_PARAMS *) dp)->X_marginal ,
                          ((RR_PARAMS *) dp)->nbins_Y ,
                          ((RR_PARAMS *) dp)->Y_bin ,
                          ((RR_PARAMS *) dp)->Y_marginal ,
                          ((RR_PARAMS *) dp)->bin_counts ) ;
      }

   ((RR_PARAMS *) dp)->crit = crit ;
   return 0 ;
}


/*
--------------------------------------------------------------------------------

   Local subroutine uses CPU threading to compute MI between one variable and
   each variable in a set

   NOTE ON THREADS... If the thread workload is low, overhead will keep CPU time
                      low.  If debug printing, one will see that only the first
                      thread keeps ending and getting replaced.  Threading behaves
                      as expected only when each thread uses a lot of CPU time.

--------------------------------------------------------------------------------
*/

static int rr_threaded (
   int type ,                   // Type of study (SCREEN_RR_? in CONST.H): continuous, tails, discrete)
   double *database ,           // Full database (this and next two lines used for continuous methods only)
   int n_vars ,                 // Number of columns in database
   int *preds ,                 // Predictor database indexes indices
   double *target ,             // Target variable, used for CONTINUOUS only
   int mcpt_reps ,              // Only for knowing whether to update progress bar
   int max_threads ,            // Maximum number of threads to use
   int ncases ,                 // Number of cases, used only for Xbin if tail_n used
   int *tail_n ,                // If non-NULL, npred vector of n for each predictor candidate, selected by Xindex
   int nX ,                     // Number of predictor candidates in Xindex below
   int *Xindex ,                // nX indices of predictors in preds, X_bin and X_marginal
   int nbins_X ,                // Number of predictor bins
   int *X_bin ,                 // Ncases vector of predictor bin indices, npred of them, selected by Xindex
   double *X_marginal ,         // Predictor marginals, npred sets of nbins_X each, selected by Xindex
   int nbins_Y ,                // Number of target bins
   int *Y_bin ,                 // Ncases vector of target bin indices (Set for each predictor if tail_n)
   double *Y_marginal ,         // Target marginal, ntarget of them (Set for each predictor if tail_n)
   double *crit ,               // Output of all criteria, npred of them
   int bins_dim ,               // nbins_X * max(nbins_X,nbins_Y)
   int *bin_counts              // Work area max_threads*bins_dim long
   )
{
   int i, k, ret_val, ix, ipred, ithread, n_threads, empty_slot ;
   char msg[4096] ;
   RR_PARAMS rr_params[MAX_THREADS] ;
   MutualInformationAdaptive *mi_adapt[MAX_THREADS] ;
   HANDLE threads[MAX_THREADS] ;

/*
   Initialize those thread parameters which are constant for all threads.
   Each thread will have its own private bin_count matrix for working storage.

   If the user specified 'continuous' then we need to allocate a
   MutualInformationAdaptive object for use by each thread.
   This object is dependent on the target,
   so we must allocate AFTER the target is shuffled.
*/

      if (type == SCREEN_RR_CONTINUOUS) {
         for (ithread=0 ; ithread<max_threads ; ithread++) {
            rr_params[ithread].type = type ;
            rr_params[ithread].database = database ;
            rr_params[ithread].n_vars = n_vars ;
            if (ithread == 0)
               mi_adapt[ithread] = new MutualInformationAdaptive ( ncases , target , 1 , 6.0 , NULL , NULL ) ;
             else
               mi_adapt[ithread] = new MutualInformationAdaptive ( ncases , target , 1 , 6.0 ,
                                                                   mi_adapt[0]->y , mi_adapt[0]->y_tied ) ;
            if (! mi_adapt[ithread]->ok  ||  mi_adapt[ithread] == NULL) {
               for (i=0 ; i<=ithread ; i++) {
                  if (mi_adapt[i] != NULL)
                     delete mi_adapt[i] ;
                  }
               audit ( "ERROR: Insufficient memory for continuous mutual information" ) ;
               return ERROR_INSUFFICIENT_MEMORY ;
               }
            rr_params[ithread].mi_adapt = mi_adapt[ithread] ;
            }
         }

      else {
         for (ithread=0 ; ithread<max_threads ; ithread++) {
            rr_params[ithread].type = type ;
            rr_params[ithread].ncases = n_cases ;   // Will be changed below if tail_n used
            rr_params[ithread].nbins_X = nbins_X ;
            rr_params[ithread].nbins_Y = nbins_Y ;
            rr_params[ithread].Y_bin = Y_bin ;            // Will be changed below if tail_n used
            rr_params[ithread].Y_marginal = Y_marginal ;  // Ditto
            rr_params[ithread].bin_counts = bin_counts + ithread * bins_dim ;
            } // For all threads, initializing constant stuff
         }


/*
   Do it
*/

   n_threads = 0 ;                    // Counts threads that are active
   for (i=0 ; i<max_threads ; i++)
      threads[i] = NULL ;


   ix = 0 ;              // Will count predictors tested
   ipred = Xindex[ix] ;  // Get its index in Xbin and Xmarginal
   empty_slot = -1 ;     // After full, will identify the thread that just completed

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
         if (type == SCREEN_RR_CONTINUOUS) {
            for (ithread=0 ; ithread<max_threads ; ithread++)
               delete mi_adapt[ithread] ;
            }
         return ERROR_ESCAPE ;
         }


/*
   Start a new thread if we still have work to do
*/

      if (ix < nX) {           // If there are still some to do
         if (empty_slot < 0)   // Negative while we are initially filling the queue
            k = n_threads ;
         else
            k = empty_slot ;
         if (tail_n != NULL) {
            rr_params[k].ncases = tail_n[ipred] ;
            rr_params[k].Y_bin = Y_bin + ipred * ncases ;
            rr_params[k].Y_marginal = Y_marginal + ipred * nbins_Y ;
            }
         rr_params[k].ix = ix  ;   // Needed for placing final result
         if (type == SCREEN_RR_CONTINUOUS)
            rr_params[k].varnum = preds[ipred] ;
         else {
            rr_params[k].X_bin = X_bin+ipred*ncases ;
            rr_params[k].X_marginal = X_marginal+ipred*nbins_X ;
            }

         threads[k] = (HANDLE) _beginthreadex ( NULL , 0 , mutinf_threaded , &rr_params[k] , 0 , NULL ) ;
         if (threads[k] == NULL) {
            audit ( "Internal ERROR: bad thread creation in RR" ) ;
            for (i=0 ; i<n_threads ; i++) {
               if (threads[i] != NULL)
                  CloseHandle ( threads[i] ) ;
               }
            return ERROR_INSUFFICIENT_MEMORY ;
            }
         ++n_threads ;
         ++ix ;
         ipred = Xindex[ix] ;  // Get its index in Xbin and Xmarginal and perhaps tail_n

         } // if (ix < nX)

      if (n_threads == 0)  // Are we done?
         break ;

/*
   Handle full suite of threads running and more threads to add as soon as some are done.
   Wait for just one thread to finish.
*/

      if (n_threads == max_threads  &&  ix < nX) {
         ret_val = WaitForMultipleObjects ( n_threads , threads , FALSE , 500000 ) ;
         if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
            sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in RR", ret_val ) ;
            audit ( msg ) ;
            return ERROR_INSUFFICIENT_MEMORY ;
            }

         crit[rr_params[ret_val].ix] = rr_params[ret_val].crit ;

         if (mcpt_reps == 1) {
            sprintf_s ( msg , "Predictor %d of %d", ix+1, nX ) ;
            title_progbar ( msg ) ;
            setpos_progbar ( (double) (ix+1) / (double) nX ) ;
            }

         empty_slot = ret_val ;
         CloseHandle ( threads[empty_slot] ) ;
         threads[empty_slot] = NULL ;
         --n_threads ;
         }

/*
   Handle all work has been started and now we are just waiting for threads to finish
*/

      else if (ix == nX) {
         ret_val = WaitForMultipleObjects ( n_threads , threads , TRUE , 500000 ) ;
         if (ret_val == WAIT_TIMEOUT  ||  ret_val == WAIT_FAILED  ||  ret_val < 0  ||  ret_val >= n_threads) {
            sprintf_s ( msg, "INTERNAL ERROR!!!  Thread wait failed (%d) in RR.CPP", ret_val ) ;
            audit ( msg ) ;
            return ERROR_INSUFFICIENT_MEMORY ;
            }

         for (i=0 ; i<n_threads ; i++) {
            crit[rr_params[i].ix] = rr_params[i].crit ;
            CloseHandle ( threads[i] ) ;
            }
         break ;
         }
      } // Endless loop which threads computation of criterion for all predictors

   if (type == SCREEN_RR_CONTINUOUS) {
      for (ithread=0 ; ithread<max_threads ; ithread++)
         delete mi_adapt[ithread] ;
      }

   return 0 ;
}

/*
--------------------------------------------------------------------------------

   Main subroutine to compute and print relevance minus redundancy study

--------------------------------------------------------------------------------
*/

int rr (
   int type ,         // Type of study (SCREEN_RR_? in CONST.H): continuous, tails, discrete)
   int npred ,        // Number of predictors
   int *preds ,       // Their indices are here
   int targetvar ,    // Index of target variable
   int nbins_pred ,   // Number of predictor bins
   int nbins_target , // Number of target bins, 0 for 2 sign-based bins
   double tail_frac , // Tail fraction
   int mcpt_type ,    // 1=complete, 2=cyclic
   int mcpt_reps ,    // Number of MCPT replications, <=1 for no MCPT
   int max_pred       // Max number of predictors in optimal subset
   )
{
   int i, j, k, n, ret_val, ivar, irep, varnum, max_threads, bins_dim ;
   int *index, *stepwise_mcpt_count, *solo_mcpt_count, *stepwise_ivar, *original_stepwise_ivar ;
   int *pred_bin, *redun_pred_bin, *target_bin, *bin_counts ;
   int *work_bin, nkept, best_ivar, *which_preds, *tail_n, *target_bin_ptr ;
   double *casework, *sorted, *mutual, *pred_thresholds, *target_thresholds, *target, *work_target ;
   double *crit, *relevance, *original_relevance, *current_crits, *sorted_crits, best_crit, dtemp ;
   double *pred_bounds, *target_bounds, *pred_marginal, *redun_pred_marginal, *target_marginal ;
   double *stepwise_crit, *original_stepwise_crit ;
   double sum_relevance, *original_sum_relevance, *sum_redundancy ;
   char msg[4096], msg2[4096] ;

   casework = NULL ;
   mutual = NULL ;
   index = NULL ;
   pred_thresholds = NULL ;
   target_thresholds = NULL ;
   pred_bin = NULL ;
   redun_pred_bin = NULL ;
   redun_pred_marginal = NULL ;
   work_bin = NULL ;
   target_bin = NULL ;
   bin_counts = NULL ;
   target = NULL ;
   tail_n = NULL ;

   if (max_pred > npred)   // Watch out for careless user
      max_pred = npred ;

   ret_val = 0 ;

   max_threads = MAX_THREADS ;

/*
   Print header
*/

   audit ( "" ) ;
   audit ( "" ) ;
   audit ( "******************************************************************************" ) ;
   audit ( "*                                                                            *" ) ;
   audit ( "* Computing relevance minus redundancy for optimal predictor subset          *" ) ;
   if (type == SCREEN_RR_CONTINUOUS)
      audit ( "*      Predictors and target are continuous                                  *" ) ;
   else if (type == SCREEN_RR_TAILS) {
      sprintf_s ( msg, "*   %5.3lf predictor tails used                                             *", tail_frac ) ;
      audit ( msg ) ;
      sprintf_s ( msg, "*      %2d target bins                                                        *", nbins_target ) ;
      audit ( msg ) ;
      }
   else if (type == SCREEN_RR_DISCRETE) {
      sprintf_s ( msg, "*      %2d predictor bins                                                     *", nbins_pred ) ;
      audit ( msg ) ;
      sprintf_s ( msg, "*      %2d target bins                                                        *", nbins_target ) ;
      audit ( msg ) ;
      }
   sprintf_s ( msg, "*   %5d predictor candidates                                               *", npred ) ;
   audit ( msg ) ;
   sprintf_s ( msg, "* %7d best predictors will be printed                                    *", max_pred ) ;
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


/*
   Allocate memory needed for all types (CONTINUOUS, TAILS, DISCRETE)
*/

   casework = (double *) malloc ( 2 * n_cases * sizeof(double) ) ;  // Pred, sorted
   sorted = casework + n_cases ;

   mutual = (double *) malloc ( 10 * npred * sizeof(double) ) ;
   crit = mutual + npred ;
   current_crits = crit + npred ;
   sorted_crits = current_crits + npred ;
   stepwise_crit = sorted_crits + npred ;
   original_stepwise_crit = stepwise_crit + npred ;
   relevance = original_stepwise_crit + npred ;
   original_relevance = relevance + npred ;
   sum_redundancy = original_relevance + npred ;
   original_sum_relevance = sum_redundancy + npred ;

   index = (int *) malloc ( 6 * npred * sizeof(int) ) ;
   stepwise_mcpt_count = index + npred ;
   solo_mcpt_count = stepwise_mcpt_count + npred ;
   which_preds = solo_mcpt_count + npred ;
   stepwise_ivar = which_preds + npred ;
   original_stepwise_ivar = stepwise_ivar + npred ;

   if (casework == NULL  ||  mutual == NULL  ||  index == NULL) {
      audit ( "ERROR: Insufficient memory for Relevance minus Redundancy" ) ;
      ret_val = ERROR_INSUFFICIENT_MEMORY ;
      goto FINISH ;
      }


/*
   For CONTINUOUS, allocate and save target
*/

   if (type == SCREEN_RR_CONTINUOUS) {
      target = (double *) malloc ( 2 * n_cases * sizeof(double) ) ;
      work_target = target + n_cases ;
      if (target == NULL) {
         audit ( "ERROR: Insufficient memory for Relevance minus Redundancy" ) ;
         ret_val = ERROR_INSUFFICIENT_MEMORY ;
         goto FINISH ;
         }
      for (i=0 ; i<n_cases ; i++)             // Extract target from database
         target[i] = database[i*n_vars+targetvar] ;
      }


/*
   For binning types (TAILS, DISCRETE), allocate that memory and compute all bin information
*/

   else if (type == SCREEN_RR_TAILS  ||  type == SCREEN_RR_DISCRETE) {
      pred_thresholds = (double *) malloc ( 2 * nbins_pred * npred * sizeof(double) ) ; // pred_thresholds, pred_marginal
      pred_marginal = pred_thresholds + npred * nbins_pred ; // Not needed for computation but nice to print for user
      pred_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ;
      work_bin = (int *) malloc ( n_cases * sizeof(int) ) ;

      if (type == SCREEN_RR_TAILS) {
         assert ( nbins_pred == 2 ) ;
         k = 3 ;  // We go trinary for redundancy
         }
      else
         k = nbins_pred ;

      if (k >= nbins_target)
         bins_dim = k * k ;
      else
         bins_dim = k * nbins_target ;
      bin_counts = (int *) malloc ( max_threads * bins_dim * sizeof(int) ) ;

      tail_n = (int *) malloc ( npred * sizeof(int) ) ;  // We use tail_n[0] if DISCRETE, so we need it for eitherz

      if (type == SCREEN_RR_TAILS) {
         target_thresholds = (double *) malloc ( 2 * nbins_target * npred * sizeof(double) ) ; // target_thresholds, target_marginal
         target_marginal = target_thresholds + nbins_target * npred ;
         target_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ; // Target bin separate for each predictor
         redun_pred_bin = (int *) malloc ( npred * n_cases * sizeof(int) ) ; // Trinary for redundancy calculation
         redun_pred_marginal = (double *) malloc ( 3 * npred * sizeof(double) ) ; // Trinary
         }
      else if (type == SCREEN_RR_DISCRETE) {
         target_thresholds = (double *) malloc ( 2 * nbins_target * sizeof(double) ) ; // target_thresholds, target_marginal
         target_marginal = target_thresholds + nbins_target ;
         target_bin = (int *) malloc ( n_cases * sizeof(int) ) ; // Target bin the same for all predictors
         }

      if (pred_thresholds == NULL  ||  target_thresholds == NULL  ||
          pred_bin == NULL  ||  work_bin == NULL  ||  target_bin == NULL  ||  bin_counts == NULL) {
         audit ( "ERROR: Insufficient memory for Relevance minus Redundancy" ) ;
         ret_val = ERROR_INSUFFICIENT_MEMORY ;
         goto FINISH ;
         }

/*
   Make an initial pass through the data to find predictor thresholds and
   permanently save bin indices for predictors and target.
   If tails-only, we must save the associated target subset indices, separately for each predictor.
   If not tails only, do target when ivar=-1.
*/

      for (ivar=-1 ; ivar<npred ; ivar++) {
         if (ivar == -1) {                   // If this is target pass
            if (type == SCREEN_RR_TAILS) // But user specified tails only
               continue ;                    // then we process the targets separately for each predictor's subset
            }
         else
            varnum = preds[ivar] ;

         if (user_pressed_escape()) {
            audit ( "ERROR: User pressed ESCape during RELEVANCE MINUS REDUNDANCY" ) ;
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
               casework[i] = database[i*n_vars+targetvar] ;
            target_bounds = target_thresholds ;
            k = nbins_target ;
            partition ( n_cases , casework , &k , target_bounds , target_bin ) ;
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

         else if (ivar >= 0  &&  type != SCREEN_RR_TAILS) {
            for (i=0 ; i<n_cases ; i++)               // Extract predictor from database
               casework[i] = database[i*n_vars+varnum] ;
            pred_bounds = pred_thresholds + ivar * nbins_pred ;
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

         // ------> Case 3: ivar>=0, TAILS: This is a predictor AND we must save the corresponding target

         else if (ivar >= 0  &&  type == SCREEN_RR_TAILS) {
            // Compute predictor bounds per tail fraction
            for (i=0 ; i<n_cases ; i++)               // Extract predictor from database
               casework[i] = database[i*n_vars+varnum] ;
            qsortd ( 0 , n_cases-1 , casework ) ;
            pred_bounds = pred_thresholds + ivar * nbins_pred ;
            k = (int) (tail_frac * (n_cases+1)) - 1 ;
            if (k < 0)
               k = 0 ;
            pred_bounds[0] = casework[k] ;
            pred_bounds[1] = casework[n_cases-1-k] ;
            // Compute and save predictor bin indices; Also save target for soon computing its bounds and indices
            n = 0 ;
            for (i=0 ; i<n_cases ; i++) {
               if (database[i*n_vars+varnum] <= pred_bounds[0]) {
                  pred_bin[ivar*n_cases+n] = 0 ;
                  redun_pred_bin[ivar*n_cases+i] = 0 ;  // Need this for intra-predictor redundancy
                  }
               else if (database[i*n_vars+varnum] >= pred_bounds[1]) {
                  pred_bin[ivar*n_cases+n] = 1 ;
                  redun_pred_bin[ivar*n_cases+i] = 1 ;
                  }
               else {
                  redun_pred_bin[ivar*n_cases+i] = 2 ;
                  continue ;
                  }
               casework[n] = database[i*n_vars+targetvar] ;
               ++n ;
               }
            tail_n[ivar] = n ;

            // Compute the target bounds based on this 'predictor tail' subset of the entire dataset
            target_bounds = target_thresholds + ivar * nbins_target ;
            k = nbins_target ;
            partition ( n , casework , &k , target_bounds , target_bin+ivar*n_cases ) ;
            if (k <nbins_target) {
               sprintf_s ( msg, "ERROR: Numerous ties reduced target bins to %d", k ) ;
               audit ( msg ) ;
               ret_val = ERROR_SYNTAX ;
               goto FINISH ;
               }
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

      if (type == SCREEN_RR_TAILS) {
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
         k = (type == SCREEN_RR_TAILS) ? 2 : nbins_pred-1 ;
         for (i=1 ; i<k ; i++) {
            sprintf_s ( msg2 , "  %12.5lf", pred_bounds[i] ) ;
            strcat_s ( msg , msg2 ) ;
            }
         if (type == SCREEN_RR_TAILS) {
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

         if (ivar==0  ||  type == SCREEN_RR_TAILS) {
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

         if (type == SCREEN_RR_TAILS) {  // Trinary
            for (i=0 ; i<3 ; i++)
               redun_pred_marginal[ivar*3+i] = 0.0 ;
            for (i=0 ; i<n_cases ; i++)
               ++redun_pred_marginal[ivar*3+redun_pred_bin[ivar*n_cases+i]] ;
            }
         }

      for (ivar=0 ; ivar<npred ; ivar++) {  // Divide counts by number of cases to get marginal

         if (type == SCREEN_UNIVAR_TAILS) {
            assert ( nbins_pred == 2 ) ;
            for (i=0 ; i<nbins_pred ; i++)
               pred_marginal[ivar*nbins_pred+i] /= tail_n[ivar] ;
            for (i=0 ; i<3 ; i++)
               redun_pred_marginal[ivar*3+i] /= n_cases ;
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

      disallow_menu = 0 ;
      mouse_cursor_arrow () ;
      end_progbar () ;
      } // If binning type (TAILS, DISCRETE)



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
*/

      if (irep) {                  // If doing permuted runs, shuffle

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
                  casework[i] = target[(i+j)%n_cases] ;
               for (i=0 ; i<n_cases ; i++)
                  target[i] = casework[i]  ;

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
-----------------------------------------------------------------------------------

   First step: Compute and save criterion for all individual candidates

-----------------------------------------------------------------------------------
*/

      for (i=0 ; i<npred ; i++)   // We'll test all candidates
         which_preds[i] = i ;

      if (type == SCREEN_RR_TAILS)
         ret_val = rr_threaded ( type , database , n_vars , preds , NULL ,
                                 mcpt_reps , max_threads , n_cases , tail_n , npred , which_preds ,
                                 nbins_pred , pred_bin , pred_marginal ,
                                 nbins_target , target_bin , target_marginal ,
                                 crit , bins_dim , bin_counts ) ;
      else
         ret_val = rr_threaded ( type , database , n_vars , preds , target ,
                                 mcpt_reps , max_threads , n_cases , NULL , npred , which_preds ,
                                 nbins_pred , pred_bin , pred_marginal ,
                                 nbins_target , target_bin , target_marginal ,
                                 crit , bins_dim , bin_counts ) ;

      if (user_pressed_escape()  &&  ret_val == 0)
         ret_val = ERROR_ESCAPE ;

      if (ret_val) {
         audit ( "ERROR: User pressed ESCape during RELEVANCE MINUS REDUNDANCY" ) ;
         goto FINISH ;
         }

/*
   The individual mutual information for each predictor has been computed and saved in crit.
   Update 'best' information for this replication.
   Print a sorted table if this is the first replication.  Else update MCPT count.
*/

      for (ivar=0 ; ivar<npred ; ivar++) {
         relevance[ivar] = crit[ivar] ;   // Will need this for Step 2, addition of more predictors
         if (ivar == 0  ||  crit[ivar] > best_crit) {
            best_crit = crit[ivar] ;
            best_ivar = ivar ;
            }
         }

      stepwise_crit[0] = best_crit ;  // Criterion for first var is largest MI
      stepwise_ivar[0] = best_ivar ;  // It's this candidate
      sum_relevance = best_crit ;

      if (irep == 0) {            // Original, unpermuted data

         original_stepwise_crit[0] = best_crit ;  // Criterion for first var is largest MI
         original_stepwise_ivar[0] = best_ivar ;  // It's this candidate
         original_sum_relevance[0] = sum_relevance ;
         stepwise_mcpt_count[0] = 1 ;             // Initialize cumulative MCPT

         // We need original_relevance for printing final table.  Other crits are just for this table.
         for (ivar=0 ; ivar<npred ; ivar++) {
            index[ivar] = ivar ;
            original_relevance[ivar] = sorted_crits[ivar] = current_crits[ivar] = crit[ivar] ;
            solo_mcpt_count[ivar] = 1 ;           // Initialize solo MCPT
            }
         qsortdsi ( 0 , npred-1 , sorted_crits , index ) ;
         audit ( "" ) ;
         audit ( "" ) ;
         sprintf_s ( msg, "Initial candidates, in order of decreasing mutual information with %s", var_names[targetvar] ) ;
         audit ( msg ) ;
         audit ( "" ) ;
         audit ( "       Variable         MI" ) ;
         audit ( "" ) ;
         for (i=npred-1 ; i>=0 ; i--) {
            k = index[i] ;
            sprintf_s ( msg, "%15s %12.4lf",
                      var_names[preds[k]], current_crits[k] ) ;
            audit ( msg ) ;
            }
         } // If irep=0 (original, unpermuted run)

      else {                                     // Count for MCPT
         if (sum_relevance >= original_sum_relevance[0])
            ++stepwise_mcpt_count[0] ;
         for (ivar=0 ; ivar<npred ; ivar++) {
            if (relevance[ivar] >= original_relevance[ivar])
               ++solo_mcpt_count[ivar] ;
            }
         } // Permuted


/*
-----------------------------------------------------------------------------------

   Second step: Iterate to add more candidates

   Note that redundancy of a candidate can change as predictors are added.
   This is because the kept set is increasing, so sum_redundancy changes.

-----------------------------------------------------------------------------------
*/

      for (i=0 ; i<npred ; i++)
         sum_redundancy[i] = 0.0 ; // sum_redundancy[i] is the total redundancy of candidate i with kept set

      for (nkept=1 ; nkept<max_pred ; nkept++) {  // Main outermost loop

/*
   Print candidates kept so far (if in unpermuted rep)
*/

         if (irep == 0) {        // Original, unpermuted
            audit ( "" ) ;
            audit ( "" ) ;
            audit ( "Predictors so far   Relevance   Redundancy   Criterion" ) ;
            audit ( "" ) ;
            for (i=0 ; i<nkept ; i++) {
               k = stepwise_ivar[i] ;
               // Cannot print sum_redundancy/nkept here because sum froze but nkept keeps increasing
               sprintf_s ( msg, "%15s %12.4lf %12.4lf %12.4lf",
                         var_names[preds[k]], relevance[k], relevance[k] - stepwise_crit[i], stepwise_crit[i] ) ;
               audit ( msg ) ;
               }
            }

/*
   Build in which_preds the candidates not yet selected
*/

         k = 0 ;                           // Candidate vector is all except those already kept
         for (i=0 ; i<npred ; i++) {
            for (j=0 ; j<nkept ; j++) {
               if (stepwise_ivar[j] == i)
                  break ;
               }
            if (j == nkept)
               which_preds[k++] = i ;
            }
         assert ( k == npred - nkept ) ;

/*
   Compute the MI of the most recently added predictor with each remaining candidate
*/

         if (user_pressed_escape()) {
            ret_val = ERROR_ESCAPE ;
            audit ( "ERROR: User pressed ESCape or other serious error during RELEVANCE MINUS REDUNDANCY" ) ;
            goto FINISH ;
            }

         k = stepwise_ivar[nkept-1] ;   // Index in preds of most recently added candidate
         if (type == SCREEN_RR_TAILS)  // redun_pred_? is trinary
            ret_val = rr_threaded ( type , database , n_vars , preds , NULL ,
                                    mcpt_reps , max_threads , n_cases , NULL , npred-nkept , which_preds ,
                                    3 , redun_pred_bin , redun_pred_marginal ,
                                    3 , redun_pred_bin+k*n_cases , redun_pred_marginal+k*3 ,
                                    crit , bins_dim , bin_counts ) ;
         else {
            if (type == SCREEN_RR_CONTINUOUS) {
               for (i=0 ; i<n_cases ; i++)
                  casework[i] = database[i*n_vars+preds[k]] ;
               }
            ret_val = rr_threaded ( type , database , n_vars , preds , casework ,
                                    mcpt_reps , max_threads , n_cases , NULL , npred-nkept , which_preds ,
                                    nbins_pred , pred_bin , pred_marginal ,
                                    nbins_pred , pred_bin+k*n_cases , pred_marginal+k*nbins_pred ,
                                    crit , bins_dim , bin_counts ) ;
            }

         if (user_pressed_escape()  &&  ret_val == 0)
            ret_val = ERROR_ESCAPE ;

         if (ret_val) {
            audit ( "ERROR: User pressed ESCape or other serious error during RELEVANCE MINUS REDUNDANCY" ) ;
            goto FINISH ;
            }
         
/*
   The redundancy of each remaining candidate with the most recently added predictor is now in crit.
   Cumulate the sum of redundancy.
   Then compute the criteria, sorting and printing if this is the unpermuted replication.
*/

         for (i=0 ; i<npred-nkept ; i++) {
            k = which_preds[i] ;   // Index in preds of this candidate
            sum_redundancy[k] += crit[i] ;
            index[i] = k ;
            sorted_crits[i] = current_crits[i] = relevance[k] - sum_redundancy[k] / nkept ;
            if (i == 0  ||  current_crits[i] > best_crit) {
               best_crit = current_crits[i] ;
               best_ivar = k ;
               }
            }

         stepwise_crit[nkept] = best_crit ;
         stepwise_ivar[nkept] = best_ivar ;
         sum_relevance += relevance[best_ivar] ;

         if (irep == 0) {        // Original, unpermuted
            original_stepwise_crit[nkept] = best_crit ;
            original_stepwise_ivar[nkept] = best_ivar ;
            original_sum_relevance[nkept] = sum_relevance ;
            stepwise_mcpt_count[nkept] = 1 ;

            qsortdsi ( 0 , npred-nkept-1 , sorted_crits , index ) ;
            audit ( "" ) ;
            audit ( "" ) ;
            audit ( "Additional candidates, in order of decreasing relevance minus redundancy" ) ;
            audit ( "" ) ;
            audit ( "       Variable     Relevance   Redundancy   Criterion" ) ;
            audit ( "" ) ;
            for (i=npred-nkept-1 ; i>=0 ; i--) {
               k = index[i] ;
               sprintf_s ( msg, "%15s %12.4lf %12.4lf %12.4lf",
                         var_names[preds[k]], relevance[k], sum_redundancy[k] / nkept,
                         relevance[k] - sum_redundancy[k] / nkept ) ;
               audit ( msg ) ;
               }
            } // If irep=0 (original, unpermuted run)

         else {                                     // Count for MCPT
            if (sum_relevance >= original_sum_relevance[nkept])
               ++stepwise_mcpt_count[nkept] ;
            } // Permuted

            
         } // Second step (for nkept): Iterate to add predictors to kept set

      } // For all MCPT replications


/*
--------------------------------------------------------------------------------

   All computation is finished.  Print.

--------------------------------------------------------------------------------
*/

   audit ( "" ) ;
   audit ( "" ) ;

/*
   Print final list of candidates and p-values
*/

   audit ( "" ) ;
   audit ( "" ) ;
   sprintf_s ( msg, "----------> Final results predicting %s <----------", var_names[targetvar] ) ;
   audit ( msg ) ;
   audit ( "" ) ;
   if (mcpt_reps > 1)
      audit ( "Final predictors    Relevance   Redundancy   Criterion    Solo pval  Group pval" ) ;
   else
      audit ( "Final predictors    Relevance   Redundancy   Criterion" ) ;
   audit ( "" ) ;
   for (i=0 ; i<nkept ; i++) {
      // Cannot print sum_redundancy/nkept here because sum froze but nkept keeps increasing
      k = original_stepwise_ivar[i] ;
      if (mcpt_reps > 1)
         sprintf_s ( msg, "%15s %12.4lf %12.4lf %12.4lf    %8.3lf    %8.3lf",
                   var_names[preds[k]], original_relevance[k], original_relevance[k] - original_stepwise_crit[i], original_stepwise_crit[i],
                   (double) solo_mcpt_count[k] / (double) mcpt_reps,
                   (double) stepwise_mcpt_count[i] / (double) mcpt_reps ) ;
      else
         sprintf_s ( msg, "%15s %12.4lf %12.4lf %12.4lf",
                   var_names[preds[k]], original_relevance[k], original_relevance[k] - original_stepwise_crit[i], original_stepwise_crit[i] ) ;
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
   if (redun_pred_bin != NULL)
      free ( redun_pred_bin ) ;
   if (redun_pred_marginal != NULL)
      free ( redun_pred_marginal ) ;
   if (work_bin != NULL)
      free ( work_bin ) ;
   if (target_bin != NULL)
      free ( target_bin ) ;
   if (bin_counts != NULL)
      free ( bin_counts ) ;
   if (target != NULL)
      free ( target ) ;
   if (tail_n != NULL)
      free ( tail_n ) ;
   return ret_val ;
}