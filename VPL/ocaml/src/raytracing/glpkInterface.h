/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
 * GlpkInterface class provides functions to access GLPK library.
 * _glp is used to store the result of simplex, and the result can be used in 
 * the next process of solving simplex. Currently it is just used 
 * in GetSatPoint(), as GetSatPoint() add the constraints incrementally.
*******************************************************************************/

#ifndef _RAYTRACING_GLPKINTER
#define _RAYTRACING_GLPKINTER

#include <glpk.h>
#include <eigen3/Eigen/Dense>
#include "polyhedron.h"

class GlpkInterface {
public:
  GlpkInterface () ;
  ~GlpkInterface () ;
  static Point GetCentralPoint (const Polyhedron& poly) ;
  Point GetSatPoint (const std::vector<int>& headIdx, const Polyhedron& poly) ;
  static bool Sat (const Polyhedron& poly, int idx) ;
  bool Simplex (const Polyhedron& poly, const VectorZ& obj, int objdir = GLP_MAX) ;
  void GetBasis () ;
  const std::vector<int>& get_basic_idx () ; 
  std::vector<int> GetNonbasicIdx () ;
  int GetVariState (int idx) ;
private:
  const double _epsilon ;  
  glp_prob* _glp ;
  std::vector<int> _basic_idx ;
} ;

#endif
