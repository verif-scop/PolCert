/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
 * Double class provides comparison method with considering the precision
 * of float point numbers
*******************************************************************************/

#ifndef _RAYTRACING_DOUBLE
#define _RAYTRACING_DOUBLE

class Double {
public:
  static bool IsLessThan(double d1, double d2) ;

  static bool AreEqual(double d1, double d2) ;
  
  static bool IsLessEq(double d1, double d2) ;
private:
  const static double _epsilon ;
} ;

#endif
