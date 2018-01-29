/****************************************************************************/
/*                                                                          */
/*  QSORT - Quick sort a double array.                                      */
/*                                                                          */
/****************************************************************************/

#include <math.h>

void qsortd ( int first , int last , double *data )
{
   int lower, upper ;
   double ftemp, split ;

   split = data[(first+last)/2] ;
   lower = first ;
   upper = last ;

   do {
      while ( split > data[lower] )
         ++lower ;
      while ( split < data[upper] )
         --upper ;
      if (lower == upper) {
         ++lower ;
         --upper ;
         }
      else if (lower < upper) {
         ftemp = data[lower] ;
         data[lower++] = data[upper] ;
         data[upper--] = ftemp ;
         }
      } while ( lower <= upper ) ;

   if (first < upper)
      qsortd ( first , upper , data ) ;
   if (lower < last)
      qsortd ( lower , last , data ) ;
}

void qsortds ( int first , int last , double *data , double *slave )
{
   int lower, upper ;
   double ftemp, split ;

   split = data[(first+last)/2] ;
   lower = first ;
   upper = last ;

   do {
      while ( split > data[lower] )
         ++lower ;
      while ( split < data[upper] )
         --upper ;
      if (lower == upper) {
         ++lower ;
         --upper ;
         }
      else if (lower < upper) {
         ftemp = slave[lower] ;
         slave[lower] = slave[upper] ;
         slave[upper] = ftemp ;
         ftemp = data[lower] ;
         data[lower++] = data[upper] ;
         data[upper--] = ftemp ;
         }
      } while ( lower <= upper ) ;

   if (first < upper)
      qsortds ( first , upper , data , slave ) ;
   if (lower < last)
      qsortds ( lower , last , data , slave ) ;
}

void qsortdsi ( int first , int last , double *data , int *slave )
{
   int lower, upper, itemp ;
   double ftemp, split ;

   split = data[(first+last)/2] ;
   lower = first ;
   upper = last ;

   do {
      while ( split > data[lower] )
         ++lower ;
      while ( split < data[upper] )
         --upper ;
      if (lower == upper) {
         ++lower ;
         --upper ;
         }
      else if (lower < upper) {
         itemp = slave[lower] ;
         slave[lower] = slave[upper] ;
         slave[upper] = itemp ;
         ftemp = data[lower] ;
         data[lower++] = data[upper] ;
         data[upper--] = ftemp ;
         }
      } while ( lower <= upper ) ;

   if (first < upper)
      qsortdsi ( first , upper , data , slave ) ;
   if (lower < last)
      qsortdsi ( lower , last , data , slave ) ;
}