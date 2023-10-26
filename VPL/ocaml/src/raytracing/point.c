/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include "point.h"

Point::Point () : _is_empty(true) {}

Point::Point (const Vector& coordinates)
  : _coordinates(coordinates), _is_empty(false) {}

void Point::set_coefficient(int var_id, double coeff) {
    _coordinates[var_id] = coeff;
}

void Point::set_coordinates (const Vector& coordinates) {
  _coordinates = coordinates ;
   _is_empty = false ;
}

Vector Point::get_coordinates (void) const {
  return _coordinates ;
}

bool Point::IsEmpty () const {
  return _is_empty ;
}

void Point::Clear () {
  _is_empty = true ;
}

std::ostream& operator<< (std::ostream& out, const Point& point)
{
  out << point._coordinates ;
  return out;
}

Point& Point::operator= (const Point& point) {
  _coordinates = point._coordinates ;
  _is_empty = point._is_empty ;
  return *this ;
}
