/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include "ray.h"

Ray::Ray (const Vector& direction) {
  _direction = direction ;
  _direction.normalize() ;
}
  
Ray::Ray (const Point& p1, const Point& p2) {
  _direction = p1.get_coordinates() - p2.get_coordinates() ;
  _direction.normalize() ;
} 

const Vector& Ray::get_direction () const {
  return _direction ;
}
