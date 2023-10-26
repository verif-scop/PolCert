/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
 * A ray starts from a point and goes to infinity along a direction.
 * As in the raytraing method all the rays start from the same point which is 
 * stored in Raytracing class, a Ray object only contains the direction.
*******************************************************************************/

#ifndef _RAYTRACING_RAY
#define _RAYTRACING_RAY

#include "point.h"
#include "polyhedron.h"

class Ray {
public:
  Ray (const Vector& direction) ;
  
  Ray (const Point& p1, const Point& p2) ;

  const Vector& get_direction () const ;

private:
  Vector _direction ;
} ;

#endif
