/******************************************************************************/
/*                                                                            */
/*  INTEGRAT - Integrate() to perform adaptive quadrature                     */
/*                                                                            */
/******************************************************************************/

#include <math.h>

#define INTBUF 100 /* Incredibly conservative! (divisions 2^(-100) are tiny!) */

double integrate (
   double low ,                // Lower limit for definite integral
   double high ,               // Upper limit
   double min_width ,          // Demand subdivision this small or smaller
   double acc ,                // Relative interval width limit
   double tol ,                // Relative error tolerance
   double (*criter) (double)   // Criterion function
   )
{
   int istack ;
   double sum, a, b, mid, fa, fb, fmid, lowres, hires, fac ;

struct IntStack {
   double x0 ;
   double x1 ;
   double f0 ;
   double f1 ;
} stack[INTBUF] ;

   fac = 3.0 * tol ; // Error is about (lowres-hires) / 3

/*
   Start by initializing the stack to be the entire interval
   and the integral so far to be zero
*/

   stack[0].x0 = low ;
   stack[0].f0 = criter ( low ) ;
   stack[0].x1 = high ;
   stack[0].f1 = criter ( high ) ;
   istack = 1 ;
   sum = 0.0 ;

/*
   Main algorithm starts here.  Pop interval off stack and test its quality.
*/

   while (istack > 0) {  // While there is still at least one interval on stack
      --istack ;         // Pop this interval
      a = stack[istack].x0 ;
      b = stack[istack].x1 ;
      fa = stack[istack].f0 ;
      fb = stack[istack].f1 ;
      mid = 0.5 * (a + b) ;
      fmid = criter ( mid ) ;
      lowres = 0.5 * (b - a) * (fa + fb) ; // Trapezoidal rule
      hires = 0.25 * (b - a) * (fa + 2.0 * fmid + fb) ; // And refined value
      // If the interval is ridiculously narrow, no point in continuing
      // If it gets this far, chances are the integrand is discontinuous
      if (b - a <= acc * (1.0 + fabs(a) + fabs(b)))
         sum += hires ;               // Quit trying to refine
      else if ((b - a) <= min_width  &&  fabs(lowres-hires) < fac * (b - a))
         sum += hires ;  // Normal convergence flag
      else {
         stack[istack].x0 = a ;
         stack[istack].f0 = fa ;
         stack[istack].x1 = mid ;
         stack[istack].f1 = fmid ;
         ++istack ;
         if (istack < INTBUF) {       // Insurance against catastrophe only
            stack[istack].x0 = mid ;  // Should ALWAYS be true (easily!)
            stack[istack].f0 = fmid ; // If this if() fails, the answer will
            stack[istack].x1 = b ;    // of course be wrong, but only due to
            stack[istack].f1 = fb ;   // a horrendous underlying problem
            ++istack ;                // like a singularity in the function
            }
         else {
            --istack ;      // Error condition, so undo push
            sum += hires ;  // And go with this best estimiate
            }
         }
      }
   return sum ;
}
