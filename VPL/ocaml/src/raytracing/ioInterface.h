/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
 * This class provides some static functions for reading or writing data.
*******************************************************************************/

#ifndef _RAYTRACING_IOINTER
#define _RAYTRACING_IOINTER

#include <vector>
#include <string>
#include "polyhedron.h"

class IoInterface {
public:
  IoInterface () ;
  std::vector<Polyhedron> LoadPolyhedra (const char* filepath) ; 
  int get_poly_num () ;
  int get_cons_num () ;
  int get_redundant_num () ;
  int get_vari_num () ;
  int get_zero_num () ;
private:
  std::string _filename ;
  int _poly_num ;
  int _cons_num ;
  int _redundant_num ;
  int _vari_num ;
  int _zero_num ;
} ;

#endif
