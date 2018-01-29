/******************************************************************************/
/*                                                                            */
/*  GLOB_MIN - Check equispaced intervals to find rough global minimum        */
/*             of a univariate function                                       */
/*                                                                            */
/*  This is called with a lower and upper bound for the domain to be          */
/*  searched.  If the function is still decreasing at one of these endpoints  */
/*  the search will continue beyond the specified endpoint.                   */
/*  The total interval is equally divided into npts-1 subintervals.           */
/*  These subintervals will be spaced arithmetically or logarithmically       */
/*  according to log_space.                                                   */
/*  If the criterion function drops to critlim or smaller, execution will     */
/*  terminate as soon as a local minimum is found.  (Global search stops.)    */
/*  Three points will be returned.  The center point, (x2,y2), will have      */
/*  smaller function value (y2) than its neighbors.  (In pathological         */
/*  cases they may be equal.)                                                 */
/*                                                                            */
/*  If npts is input negative, that means the user is inputting f(low) in *y2.*/
/*  This sometimes saves a function evaluation.                               */
/*                                                                            */
/*  Normally it returns zero.  It returns one if user pressed ESCape before   */
/*  the minimum was found.                                                    */
/*                                                                            */
/******************************************************************************/

#include <math.h>

int user_pressed_escape() ;

int glob_min (
   double low ,           // Lower limit for search
   double high ,          // Upper limit
   int npts ,             // Number of points to try
   int log_space ,        // Space by log?
   double critlim ,       // Quit global if crit drops this low
   int (*criter) (double , double *) , // Criterion function
   double *x1 ,
   double *y1 ,           // Lower X value and function there
   double *x2 ,
   double *y2 ,           // Middle (best)
   double *x3 ,
   double *y3             // And upper
   )
{
   int i, ibest, turned_up, know_first_point, user_quit ;
   double x, y, rate, previous ;

   user_quit = 0 ;

   if (npts < 0) {
      npts = -npts ;
      know_first_point = 1 ;
      }
   else 
      know_first_point = 0 ;

   if (log_space)
      rate = exp ( log (high / low) / (npts - 1) ) ;
   else 
      rate = (high - low) / (npts - 1) ;

   x = low ;

   previous = 0.0 ; // Avoids "use before set" compiler warnings
   ibest = -1 ;     // For proper critlim escape
   turned_up = 0 ;  // Must know if function increased after min

   for (i=0 ; i<npts ; i++) {

      if (i  ||  ! know_first_point)
         user_quit = criter ( x , &y ) ;
      else
         y = *y2 ;

      if ((i == 0)  ||  (y < *y2)) {  // Keep track of best here
         ibest = i ;
         *x2 = x ;
         *y2 = y ;
         *y1 = previous ;  // Function value to its left
         turned_up = 0 ;   // Flag that min is not yet bounded
         }

      else if (i == (ibest+1)) { // Didn't improve so this point may
         *y3 = y ;               // be the right neighbor of the best
         turned_up = 1 ;         // Flag that min is bounded
         }

      previous = y ;             // Keep track for left neighbor of best

      if (! user_quit)
         user_quit = user_pressed_escape () ;

      if ((user_quit  ||  (*y2 <= critlim))  &&  (ibest > 0)  &&  turned_up)
         break ; // Done if (abort or good enough) and both neighbors found

      if (user_quit)          // Alas, both neighbors not found
         return user_quit ;   // Flag that the other 2 pts not there

      if (log_space)
         x *= rate ;
      else 
         x += rate ;
      }

/*
   At this point we have a minimum (within low,high) at (x2,y2).
   Compute x1 and x3, its neighbors.
   We already know y1 and y3 (unless the minimum is at an endpoint!).
*/

   if (log_space) {
      *x1 = *x2 / rate ;
      *x3 = *x2 * rate ;
      }
   else {
      *x1 = *x2 - rate ;
      *x3 = *x2 + rate ;
      }

/*
   Normally we would now be done.  However, the careless user may have
   given us a bad x range (low,high) for the global search.
   If the function was still decreasing at an endpoint, bail out the
   user by continuing the search.
*/

   if (! turned_up) { // Must extend to the right (larger x)
      for (;;) {      // Endless loop goes as long as necessary

         user_quit = user_pressed_escape () ;

         if (! user_quit)
            user_quit = criter ( *x3 , y3 ) ;

         if (user_quit)          // Alas, both neighbors not found
            return user_quit ;   // Flag that the other 2 pts not there

         if (*y3 > *y2)  // If function increased we are done
            break ;
         if ((*y1 == *y2)  &&  (*y2 == *y3)) // Give up if flat
            break ;

         *x1 = *x2 ;      // Shift all points
         *y1 = *y2 ;
         *x2 = *x3 ;
         *y2 = *y3 ;

         rate *= 3.0 ;    // Step further each time
         if (log_space)   // And advance to new frontier
            *x3 *= rate ;
         else 
            *x3 += rate ;
         }
      }

   else if (ibest == 0) {  // Must extend to the left (smaller x)
      for (;;) {           // Endless loop goes as long as necessary

         user_quit = user_pressed_escape () ;

         if (! user_quit)
            user_quit = criter ( *x1 , y1 ) ;

         if (user_quit)         // Alas, both neighbors not found
            return user_quit ;  // Flag that the other 2 pts not there

         if (*y1 > *y2)   // If function increased we are done
            break ;
         if ((*y1 == *y2)  &&  (*y2 == *y3)) // Give up if flat
            break ;

         *x3 = *x2 ;      // Shift all points
         *y3 = *y2 ;
         *x2 = *x1 ;
         *y2 = *y1 ;

         rate *= 3.0 ;    // Step further each time
         if (log_space)   // And advance to new frontier
            *x1 /= rate ;
         else 
            *x1 -= rate ;
         }
      }

   return 0 ;
}
