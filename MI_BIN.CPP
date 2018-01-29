/******************************************************************************/
/*                                                                            */
/*  MI_BIN - Mutual information for binary predicted and predictors           */
/*                                                                            */
/******************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <conio.h>
#include <ctype.h>
#include <stdlib.h>

extern void free_data ( int nvars , char **names , double *data ) ;
extern double mutinf_b ( int n , short int *y , short int *x , short int *z ) ;
extern int readfile ( char *name , int *nvars , char ***names ,
                      int *ncases , double **data ) ;
extern void partition ( int n , double *data , int *npart ,
                        double *bnds , short int *bins ) ;
extern void qsortdsi ( int first , int last , double *data , int *slave ) ;

int main (
   int argc ,    // Number of command line arguments (includes prog name)
   char *argv[]  // Arguments (prog name is argv[0])
   )

{
   int i, j, k, depzero, indepzero, nvars, ncases, maxkept, ivar, *kept ;
   int n_indep_vars, idep, icand, iz, ibest, *sortwork, nkept, *last_indices ;
   double *data, *work, temp, p, error_entropy ;
   double *save_info, bestcrit ;
   double criterion, entropy, bound, *crits, *scores ;
   short int *bins_dep, *bins_indep, *xbins ;
   char filename[256], **names, depname[256] ;
   char trial_name[256] ;
   FILE *fp ;

/*
   Process command line parameters
*/

#if 1
   if (argc != 7) {
      printf ( "\nUsage: MI_BIN  datafile  n_indep  depname  depzero  indepzero  maxkept" ) ;
      printf ( "\n  datafile - name of the text file containing the data" ) ;
      printf ( "\n             The first line is variable names" ) ;
      printf ( "\n             Subsequent lines are the data." ) ;
      printf ( "\n             Delimiters can be space, comma, or tab" ) ;
      printf ( "\n  n_indep - Number of independent vars, starting with the first" ) ;
      printf ( "\n  depname - Name of the 'dependent' variable" ) ;
      printf ( "\n            It must be AFTER the first n_indep variables" ) ;
      printf ( "\n  depzero - If nonzero, dependent variable is split >0 vs <=0" ) ;
      printf ( "\n            Else split is by optimal partition" ) ;
      printf ( "\n  indepzero - Ditto, for independent variables" ) ;
      printf ( "\n  maxkept - Stepwise will allow at most this many predictors" ) ;
      return EXIT_FAILURE ;
      }

   strcpy ( filename , argv[1] ) ;
   n_indep_vars = atoi ( argv[2] ) ;
   strcpy ( depname , argv[3] ) ;
   depzero = atoi ( argv[4] ) ;
   indepzero = atoi ( argv[5] ) ;
   maxkept = atoi ( argv[6] ) ;
#else
   strcpy ( filename , "..\\VARS.TXT" ) ;
   strcpy ( depname , "DAY_RETURN" ) ;
   n_indep_vars = 8 ;
   depzero = 1 ;
   indepzero = 1 ;
   maxkept = 99 ;
#endif

   _strupr ( depname ) ;


/*
   Open the text file to which results will be written
*/

   fp = fopen ( "MI_BIN.LOG" , "wt" ) ;
   if (fp == NULL) { // Should never happen
      printf ( "\nCannot open MI_BIN.LOG file for writing!" ) ;
      return EXIT_FAILURE ;
      }

/*
   Read the file and locate the index of the 'dependent' variable
*/

   if (readfile ( filename , &nvars , &names , &ncases , &data ))
      return EXIT_FAILURE ;

   for (idep=0 ; idep<nvars ; idep++) {
      if (! strcmp ( depname , names[idep] ))
         break ;
      }

   if (idep == nvars) {
      printf ( "\nERROR... Dependent variable %s is not in file", depname ) ;
      return EXIT_FAILURE ;
      }

   if (idep < n_indep_vars) {
      printf ( "\nERROR... Dependent variable %s must be beyond independent vars",
               depname ) ;
      return EXIT_FAILURE ;
      }

/*
   Allocate scratch memory

   bins_dep - Bin ids for the 'dependent' variable
   bins_indep - Bin ids for the 'independent' variables
   kept - Array of indices of variables kept so far
   crits - Ditto, criterion
   scores - Current (regularly updated) min I(Y;X|Z) for choosing best candidate
   last_indices - For each candidate, last index among Zs used to compute scores
   sortwork - Temporary use for printing variable's information sorted
   save_info - Ditto, this is univariate information, to be sorted
*/

   work = (double *) malloc ( ncases * sizeof(double) ) ;
   assert ( work != NULL ) ;
   bins_dep = (short int *) malloc ( ncases * sizeof(short int) ) ;
   assert ( bins_dep != NULL ) ;
   bins_indep = (short int *) malloc ( ncases * n_indep_vars * sizeof(short int) ) ;
   assert ( bins_indep != NULL ) ;
   kept = (int *) malloc ( n_indep_vars * sizeof(int) ) ;
   assert ( kept != NULL ) ;
   crits = (double *) malloc ( n_indep_vars * sizeof(double) ) ;
   assert ( crits != NULL ) ;
   scores = (double *) malloc ( n_indep_vars * sizeof(double) ) ;
   assert ( scores != NULL ) ;
   last_indices = (int *) malloc ( n_indep_vars * sizeof(int) ) ;
   assert ( last_indices != NULL ) ;
   sortwork = (int *) malloc ( n_indep_vars * sizeof(int) ) ;
   assert ( sortwork != NULL ) ;
   save_info = (double *) malloc ( n_indep_vars * sizeof(double) ) ;
   assert ( save_info != NULL ) ;

/*
   Compute the bin membership of all variables.
   If the user requested, we treat the variable as binary (two bins)
   using <=0 and >0 as the definition of bin membership.
   Otherwise we use partition() to do the split.
*/

   if (depzero) {   // The dependent variable is split at zero
      for (i=0 ; i<ncases ; i++) {
         if (data[i*nvars+idep] > 0.0)
            bins_dep[i] = (short int) 1 ;
         else
            bins_dep[i] = (short int) 0 ;
         }
      fprintf ( fp , "\n%s has been split at zero", names[idep] ) ;
      }
   else {                  // The dependent variable is to be partitioned
      for (i=0 ; i<ncases ; i++)
         work[i] = data[i*nvars+idep] ;
      k = 2 ;
      partition ( ncases , work , &k , NULL , bins_dep ) ;
      fprintf ( fp , "\n%s has been optimally partitioned", names[idep] ) ;
      }

   if (indepzero) {   // The independent variable is split at zero
      fprintf ( fp , "\nIndependent variables have been split at zero");
      for (ivar=0 ; ivar<n_indep_vars ; ivar++) {
         for (i=0 ; i<ncases ; i++) {
            if (data[i*nvars+ivar] > 0.0)
               bins_indep[ivar*ncases+i] = (short int) 1 ;
            else
               bins_indep[ivar*ncases+i] = (short int) 0 ;
            }
         }
      }
   else {
      fprintf ( fp , "\nIndependent variables have been given an optimal split");
      for (ivar=0 ; ivar<n_indep_vars ; ivar++) {
         for (i=0 ; i<ncases ; i++)
            work[i] = data[i*nvars+ivar] ;
         k = 2 ;
         partition ( ncases , work , &k , NULL , bins_indep+ivar*ncases ) ;
         }
      }

/*
   Compute and save the mutual information for the dependent variable with
   each individual independent variable candidate.  Print the results,
   sort them, and print them again, this time sorted.
   Also compute the error entropy so we can use it for the Fano bound.
   We need to save the criterion of each in save_info because this is the array
   that will be sorted, and we also save it in scores because this is the array
   that will be used for future 'best variable' selection.
   While we're at it, initialize last_indices to -1 for each variable.
   This is explained in the big comment block later.
*/

   entropy = mutinf_b ( ncases , bins_dep , NULL , NULL ) ;
   fprintf ( fp , "\n\n\nMutual information of %s  (Entropy = %.4lf)",
             depname, entropy ) ;

   fprintf ( fp , "\n\nInitial candidates, in order of appearance in data file" ) ;
   fprintf ( fp , "\n" ) ;
   fprintf ( fp , "\n                       Variable   Information   Fano's bound" ) ;

   for (icand=0 ; icand<n_indep_vars ; icand++) { // Try all candidates
      xbins = bins_indep + icand * ncases ; // This X candidate is here

      // Compute the error entropy
      k = 0 ;
      for (i=0 ; i<ncases ; i++) {
         if (bins_dep[i] == xbins[i])
            ++k ;
         }
      if (k > 0  &&  k < ncases) {
         p = (double) k / (double) ncases ;
         error_entropy = -p * log(p) - (1.0 - p) * log(1.0-p) ;
         }
      else
         error_entropy = 0.0 ;

      criterion = mutinf_b ( ncases , bins_dep , xbins , NULL ) ;
      bound = (entropy - criterion - error_entropy) / log ( 2.0 ) ;
      if (bound < 0.0)
         bound = 0.0 ;
      printf ( "\n%s = %.5lf  (%.5lf)", names[icand], criterion, bound ) ;
      fprintf ( fp , "\n%31s %11.5lf  %13.5lf", names[icand], criterion, bound ) ;
      sortwork[icand] = icand ;
      scores[icand] = save_info[icand] = criterion ;
      last_indices[icand] = -1 ;
      } // Initial list of all candidates


   fprintf ( fp , "\n" ) ;
   fprintf ( fp , "\nInitial candidates, in order of decreasing mutual information" ) ;
   fprintf ( fp , "\n" ) ;
   fprintf ( fp , "\n                       Variable   Information" ) ;

   qsortdsi ( 0 , n_indep_vars-1 , save_info , sortwork ) ;
   for (icand=0 ; icand<n_indep_vars ; icand++) { // Do all candidates
      k = sortwork[n_indep_vars-1-icand] ;        // Index of sorted candidate
      fprintf ( fp , "\n%31s   %.5lf", names[k], save_info[n_indep_vars-1-icand] ) ;
      }

/*
   Initialize the 'kept' set to be the best variable, and then begin the
   main outer loop that adds variables one at a time.

   The criterion for picking the best next candidate (we want the max criterion)
   is the minimum value of I(Y;X|Z) across the set of variables kept so far.
   In this expression, Y is the dependent variable, X is the candidate, and
   Z is a member of the kept set.  I(Y;X|Z) is large when X adds information
   about Y above and beyond what Z already adds.  It is small if X adds nothing
   useful.  So by letting Z be each member of the kept set, one at a time,
   and using the minimum I(Y;X|Z) found, we avoid adding a new variable whose
   information is already supplied.

   There is a cute trick for avoiding having to check every candidate against
   every Z.  When a new Z is tested in computing the minimum across all Z,
   the minimum obviously cannot increase.  So if the minimum across Z so far
   is already worse than the best candidate criterion so far, there is no
   point in continuing to test more Zs for a candidate.  This candidate has
   already lost the competition for this round.  Of course, we need to keep
   track of, for each candidate, the place where we have stopped testing it
   against Zs.  This is because on a later round of adding a variable, the
   best so far may be small, and a candidate whose testing was stopped early
   on a prior round may need to be tested against more Zs to see if it might
   be the best now.
*/

   kept[0] = sortwork[n_indep_vars-1] ;   // Index of best single candidate
   crits[0] = save_info[n_indep_vars-1] ; // Its criterion value
   nkept = 1 ;

   if (maxkept > n_indep_vars)  // Guard against silly user
      maxkept = n_indep_vars ;

   while (nkept < maxkept) {

      printf ( "\n\nLatest candidate: %s", names[kept[nkept-1]] ) ;

      fprintf ( fp , "\n" ) ;
      fprintf ( fp , "\nVariables so far                 Criterion" ) ;
      for (i=0 ; i<nkept ; i++)
         fprintf ( fp , "\n%31s %10.5lf", names[kept[i]], crits[i] ) ;
      fprintf ( fp , "\n" ) ;
      fprintf ( fp , "\nSearching for an additional candidate..." ) ;
      fprintf ( fp , "\n" ) ;
      fprintf ( fp , "\n                       Variable  Criterion" ) ;

      bestcrit = -1.e60 ;
      for (icand=0 ; icand<n_indep_vars ; icand++) { // Try all candidates
         for (i=0 ; i<nkept ; i++) {  // Is this candidate already kept?
            if (kept[i] == icand)
               break ;
            }
         if (i < nkept)  // If this candidate 'icand' is already kept
            continue ;   // Skip it

         strcpy ( trial_name , names[icand] ) ;   // Its name for printing
         printf ( "\n  Testing candidate %s  Starting score=%.5lf  Tested thru %d",
                  trial_name, scores[icand], last_indices[icand] ) ;

         // Compute I(Y;X|Z) for each Z in the kept set, and keep track of min
         // We've already done them through last_indices[icand], so start
         // with the next one up.  Allow for early exit if icand already loses.
         for (iz=last_indices[icand]+1 ; iz<nkept ; iz++) {
            if (scores[icand] <= bestcrit) // Has this candidate already lost?
               break ;                     // If so, no need to keep doing Zs
            j = kept[iz] ;                 // Index of variable in the kept set
            temp = mutinf_b ( ncases , bins_dep , bins_indep + icand * ncases ,
                              bins_indep + j * ncases ) ; // I(Y;X|Z)
            if (temp < scores[icand])
               scores[icand] = temp ;
            last_indices[icand] = iz ;
            printf ( "\n    With kept %s I(Y;X|Z)=%.5lf  score=%.5lf",
                     names[j], temp, scores[icand] ) ;
            } // For all kept variables, computing min conditional mutual information

         criterion = scores[icand] ;
         printf ( "\n  %s = %.5lf", trial_name, criterion ) ;
         fprintf ( fp , "\n%31s %10.5lf", trial_name, criterion ) ;

         if (criterion > bestcrit) { // Did we just set a new record?
            bestcrit = criterion ;   // If so, update the record
            ibest = icand ;          // Keep track of the winning candidate
            }

         } // For all candidates

      // We now have the best candidate
      if (bestcrit <= 0.0)
         break ;
      kept[nkept] = ibest ;
      crits[nkept] = bestcrit ;
      printf ( "\nAdded %s = %.5lf", names[ibest], bestcrit ) ;
      ++nkept ;
      } // While adding new variables

   fprintf ( fp , "\n" ) ;
   fprintf ( fp , "\nFinal set                        Criterion" ) ;
   for (i=0 ; i<nkept ; i++)
      fprintf ( fp , "\n%31s %10.5lf", names[kept[i]], crits[i] ) ;


   fclose ( fp ) ;
   free ( work ) ;
   free ( bins_dep ) ;
   free ( bins_indep ) ;
   free ( kept ) ;
   free ( crits ) ;
   free ( scores ) ;
   free ( last_indices ) ;
   free ( sortwork ) ;
   free ( save_info ) ;
   free_data ( nvars , names , data ) ;
   printf ( "\n\nPress any key..." ) ;
   _getch () ;
   return EXIT_SUCCESS ;
}
