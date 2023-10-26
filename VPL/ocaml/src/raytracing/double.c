#include "double.h"

/*******************************************************************************
 * @return true if d1 is less than d2
*******************************************************************************/
bool Double::IsLessThan(double d1, double d2) {
   return d1 + _epsilon < d2 ;  
}

/*******************************************************************************
 * @return true if d1 is equal to d2
*******************************************************************************/
bool Double::AreEqual(double d1, double d2) {
  double diff = d1 - d2 ;
  return (diff < _epsilon && diff > - _epsilon) ;
}
  
/*******************************************************************************
 * @return true if d1 is less than d2 or d1 is equal to d2
*******************************************************************************/
bool Double::IsLessEq(double d1, double d2) {
  bool res = IsLessThan(d1, d2) || AreEqual(d1, d2) ;
  return res ;  
}

const double Double::_epsilon = 1e-10 ;
