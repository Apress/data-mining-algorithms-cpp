/******************************************************************************/
/*                                                                            */
/*  POWELL - Use Powell's method to find a local minimum of a function        */
/*           Note that we must provide in y the function value at starting x. */
/*                                                                            */
/******************************************************************************/

#include <math.h>

extern int brentmin ( int itmax , double critlim , double eps ,
                      double tol , int (*criter) (double , double *) ,
                      double *x1 , double *x2 , double *x3 , double *y ) ;
extern int glob_min ( double low , double high , int npts , int log_space ,
                      double critlim , int (*criter) (double , double *) ,
                      double *x1, double *y1 , double *x2, double *y2 ,
                      double *x3, double *y3 ) ;
extern int user_pressed_escape () ;

/*
   This routine uses the general univariate minimizers 'glob_min' and
   'brentmin' to minimize along the gradient line. So we must have a local
   function for them to call, and it must have access to the relevant data.
   These statics handle that.
*/

static int univar_crit ( double t , double *fval ) ; // Local univariate criterion
static double *local_x, *local_base, *local_direc ;  // It uses these
static int local_n ;
static int (*local_criter) ( double *xvec , double *fval ) ;

int powell (
   double scale ,         // Used for size of initial search by glob_min()
   int maxits ,           // Iteration limit (0 for no limit)
   double critlim ,       // Quit if crit drops this low
   double tol ,           // Convergence tolerance
   int (*criter) ( double * , double * ) , // Criterion func
   int n ,                // Number of variables
   double *x ,            // In/out of independent variable
   double *y ,            // In/out of function value
   double *base ,         // Work vector n long
   double *p0 ,           // Work vector n long
   double *direc ,        // Work vector n*n long
   int update_progress    // Call setpos_progress_message() to update progress bar?
   )
{
   int i, j, idir, iter, user_quit, convergence_counter, idelta, replaced ;
   double fval, fbest, f0, test, t1, t2, t3, y1, y2, y3 ;
   double prev_best, toler, delta, len, ftest, mult ;

   t2 = 0.0 ;  // Not needed.  Shuts up LINT.

/*
   Initialize for the local univariate criterion which may be called by
   'glob_min' and 'brentmin' to minimize along the search direction.
*/


   local_x = x ;
   local_base = base ;
   local_n = n ;
   local_criter = criter ;

/*
   Initialize the direction matrix to be an identity.
*/

   for (i=0 ; i<n ; i++) {
      for (j=0 ; j<n ; j++)
         direc[i*n+j] = (j == i) ? 1.0 : 0.0 ;
      }

/*
   Main loop.  For safety we impose a limit on iterations.
*/

   replaced = -1 ;          // Assume no replacement will be done
   prev_best = 1.e90 ;
   fbest = *y ;
   iter = convergence_counter = user_quit = 0 ;

   for (;;) {

      if ((iter++ >= maxits)  &&  (maxits > 0))
         break ;

      if (fbest < critlim)     // Do we satisfy user yet?
         break ;

/*
   Convergence check
*/

      if (fabs(prev_best) <= 1.0)            // If the function is small
         toler = tol ;                       // Work on absolutes
      else                                   // But if it is large
         toler = tol * fabs(prev_best) ;     // Keep things relative

      if ((prev_best - fbest)  <=  toler) {  // If little improvement
         if (++convergence_counter >= 2)     // Then count how many
            break ;                          // And quit if too many
         }
      else                                   // But a good iteration
         convergence_counter = 0 ;           // Resets this counter

      if (fbest < prev_best)                 // Always true if well behaved
         prev_best = fbest ;

/*
   Does the user want to quit?
*/

      if ((user_quit = user_pressed_escape ()) != 0)
         break ;

/*
   Loop over all search directions, minimizing in each.
   Keep track of the direction that gave the most improvement.
   For efficiency, we keep 'replaced' as the vector that just got replaced
   (or -1 if no replacement was done).  Skip the first direction if that
   was the one just replaced!
*/

      for (i=0 ; i<n ; i++)            // Preserve the starting point
         p0[i] = x[i] ;
      f0 = fbest ;                     // And function value at that point
      delta = -1.0 ;                   // Will keep best improvement here
      idelta = 0 ;                     // Shuts up LINT

      for (idir=0 ; idir<n ; idir++) { // For each direction
         if ((n>1)  &&  ! idir  &&  ! replaced) // If we just replaced the
            continue ;                 // first vector, avoid waste
         for (i=0 ; i<n ; i++)         // Local criter steps out from here
            base[i] = x[i] ;           // So it must be current point
         y2 = fbest ;                  // Glob_min can use first f value
         local_direc = direc + idir * n ; // This is the idir direction
         for (mult=1.0 ; mult < 101.0 ; mult *= 10.0) {
            user_quit = glob_min ( -mult * scale , mult * scale , 7 , 0 ,
                                   critlim , univar_crit , &t1 , &y1 , &t2 ,
                                   &y2 , &t3 , &y3 ) ;
            if (user_quit)  // ESCape?
               break ;
            if ((y2 < y1)  &&  (y2 < y3)) // Loop until minimum is bounded
               break ;
            }
         if (user_quit  ||  (y2 < critlim)) { // ESCape or good enough already?
            if (y2 < fbest) {                 // If global caused improvement
               for (i=0 ; i<n ; i++)          // Implement that improvement
                  x[i] = base[i] + t2 * local_direc[i] ;
               fbest = y2 ;
               }
            else {                            // Else revert to starting point
               for (i=0 ; i<n ; i++)
                  x[i] = base[i] ;
               }
            goto FINISH ;
            }

         if (convergence_counter) { // If failing, try extra hard
            fval = y2 ;
            user_quit = brentmin ( 20 , critlim , tol , 1.e-7 ,
                              univar_crit , &t1 , &t2 , &t3 , &fval ) ;
            }
         else {                    // But normally refine only moderately
            fval = y2 ;
            user_quit = brentmin ( 10 , critlim , 10.0 * tol , 1.e-5 ,
                              univar_crit , &t1 , &t2 , &t3 , &fval ) ;
            }
         if (user_quit)
            goto FINISH ;

         for (i=0 ; i<n ; i++)          // Get current point from parametric
            x[i] = base[i] + t2 * local_direc[i] ;

         if (fbest - fval > delta) {    // Keep track of best direction
            delta = fbest - fval ;
            idelta = idir ;
            }
         fbest = fval ;                  // This is always the best so far
         } // For all directions

/*
   Before looping through all n directions, we stood at point p0 with f=f0.
   We now stand at point x with f=fbest.
   It is quite possible that the average direction of motion points right
   along a ravine.  Thus, it behooves us to step out in that direction.
   Try it.  We might luck out.
*/

      for (i=0 ; i<n ; i++) {
         p0[i] = x[i] - p0[i] ;    // Preserve average direction here
         base[i] = x[i] + p0[i] ;  // Step out to this point (borrow base)
         }
      user_quit = criter ( base , &fval ) ;     // Evaluate function at this test point

      if (user_quit)
         goto FINISH ;

/*
   If this step improved, and if a more sophisticated second derivative
   test is passed, we replace the old direction of max improvement with this
   average direction (after first minimizing in this great direction).
   Also, set 'replaced' to the vector that was replaced if that is done.
   Otherwise set it to -1.  We do that so on the next iteration we skip
   minimization along the first direction if that happened to be the one
   that was just replaced!
*/

      replaced = -1 ;                  // Assume no replacement will be done
      ftest = fbest ;                  // Save for replacement test
      if (fval < fbest) {              // If this trial step improved
         fbest = fval ;                // Might as well keep this better point
         for (i=0 ; i<n ; i++)         // Keep x current
            x[i] = base[i] ;
         }

      if (fval < f0) {                 // First of two tests for replacement
         test = f0 - ftest - delta ;
         test = 2.0 * (f0 - 2.0 * ftest + fval) * test * test ;
         if (test < delta * (f0 - fval) * (f0 - fval)) { // Use this direction
            replaced = idelta ;        // Record this upcoming replacement
            len = 0.0 ;                // Will cumulate length of new dir
            for (i=0 ; i<n ; i++)
               len += p0[i] * p0[i] ;
            len = sqrt ( len ) ;
            for (i=0 ; i<n ; i++)
               p0[i] /= len ;          // Keep direction unit length
            local_direc = p0 ;         // We put the average direction here 
            y2 = fbest ;               // Glob_min can use first f value
            for (i=0 ; i<n ; i++)      // Set out from here
               base[i] = x[i] ;
            for (mult=1.0 ; mult < 101.0 ; mult *= 10.0) {
               user_quit = glob_min ( -mult * scale , mult * scale , 7 , 0 ,
                                      critlim , univar_crit , &t1 , &y1 , &t2 ,
                                      &y2 , &t3 , &y3 ) ;
               if (user_quit)  // ESCape?
                  break ;
               if ((y2 < y1)  &&  (y2 < y3)) // Loop until minimum is bounded
                  break ;
               }
            if (user_quit  ||  (y2 < critlim)) { // ESCape or good enough already?
               if (y2 < fbest) {                 // If global caused improvement
                  for (i=0 ; i<n ; i++)          // Implement that improvement
                     x[i] = base[i] + t2 * local_direc[i] ;
                  fbest = y2 ;
                  }
               else {                            // Else revert to starting point
                  for (i=0 ; i<n ; i++)
                     x[i] = base[i] ;
                  }
               break ;
               }
            if (convergence_counter) {  // If failing, try extra hard
               fval = y2 ;
               user_quit = brentmin ( 20 , critlim , tol , 1.e-7 ,
                                 univar_crit , &t1 , &t2 , &t3 , &fval ) ;
               }
            else {                    // But normally refine only moderately
               fval = y2 ;
               user_quit = brentmin ( 10 , critlim , 10.0 * tol , 1.e-5 ,
                                 univar_crit , &t1 , &t2 , &t3 , &fval ) ;
               }
            if (user_quit) {              // If user pressed ESCape
               fbest = -fval ;
               user_quit = 1 ;
               goto FINISH ;
               }

            for (i=0 ; i<n ; i++)          // Get current point from parametric
               x[i] = base[i] + t2 * local_direc[i] ;
            fbest = fval ;                 // This is always the best so far

            for (i=0 ; i<n ; i++)
               direc[idelta*n+i] = p0[i] ; // Replace best direction with this
            } // If second derivative test passed
         } // If test one passed
      } // Main loop

FINISH:

      *y = fbest ;
      return user_quit ;
}


/*
--------------------------------------------------------------------------------

   local criterion for univariate minimization

--------------------------------------------------------------------------------
*/

static int univar_crit ( double t , double *fval )
{
   int i ;

   for (i=0 ; i<local_n ; i++)
      local_x[i] = local_base[i] + t * local_direc[i] ;
   return local_criter ( local_x , fval ) ;
}
