/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
 * A polyhedron contains many constraints in the form:
 * a_1 x_1 + a_2 x_2 + ... + a_n x_n <op> b, where <op> is <, <= or =, and 
 * b is a constant. <op> is stored in _operators, and 0 means "<", 1 means "<="
 * and 2 means "=".
 * The matrix _coefficients stores the coefficients of the variables, and the
 * vector _constants stores the constant in each row 
 * _central_point is a point inside of the polyhedron, and the sum of distance 
 * from this point to each facet of the polyhedron is minimized.
 * _active_table is used to mark redundancy now, i.e. its ith value is true if
 * the ith constraint is irredundant. 
 * A witness point for constraint Ci is a point which violates Ci and satisfies 
 * the other constraints. We sotre the direction of the ray which reaches the
 * witness point from the central point while minimizing the polyhedra. If the
 * witness points are need, we can compute them as we know the ray. (We do not
 * compute the witness points during minimization to make the minimization 
 * process be efficient. Besides not all the cases of minimization require the
 * witness points). 
*******************************************************************************/

#ifndef _RAYTRACING_POLYHEDRON
#define _RAYTRACING_POLYHEDRON

#include <vector>
#include <map>
#include <eigen3/Eigen/Dense>
#include "point.h"

#ifdef _OPENMP
#define VERIMAG_POLYHEDRA_MINIMIZE_OPENMP
#else
#ifdef __cilk
#define VERIMAG_POLYHEDRA_MINIMIZE_CILK
#endif
#endif

typedef Eigen::MatrixXd Matrix ;
typedef Eigen::VectorXd Vector ;
typedef Eigen::VectorXi VectorZ ;
enum {REDUNDANT = 0, IRREDUNDANT = 1, DUPLICATED = 2} ;

class Polyhedron {
public:
  Polyhedron (int consNum, int variNum) ; 
  Polyhedron (Polyhedron&& from) = default ;
  Polyhedron& operator= (const Polyhedron& from) = delete ;
  Polyhedron& operator= (Polyhedron&& from) = default ;
  void Init() ;
  bool Minimize () ;
  void MinimizeSimple () ;
  Polyhedron GetMinimizedPoly () ;
  Polyhedron GetSubPoly (const std::vector<int>& indexVec) ;
  bool Include (const Polyhedron& poly) ;
  Polyhedron Combine (const Polyhedron& poly1) ;
  bool Satisfy (const Point& point, int index) ;
  void GetDuplicateIdx () ;
  bool ConstraintsEq (int idx1, int idx2) ;
  int get_variable_num () const ;
  void set_variable_num (int num) ;
  int get_constraint_num () const ;
  void set_constraint_num (int num) ; 
  int get_redundant_num () const ;
  void set_redundant_num (int num) ; 
  int get_zero_num () const ;
  void set_zero_num (int num) ; 
  int get_generator_num () const ;
  void set_generator_num (int num) ; 
  int get_id () const ;
  void set_id (int id) ; 
  std::vector<int> GetActiveIdx () ;
  std::vector<int> GetInactiveIdx () ;
  bool IsActive (int consIdx) const ;
  void set_central_point (const Point& point) ;
  Point get_central_point () const ; 
  Vector GetConstraint (int consIdx) const ;
  void SetConstraint (int consIdx, const Vector& cons) ;
  double GetConstant (int consIdx) const ;
  void SetConstant (int consIdx, double val) ;
  int GetOperator (int consIdx) const ;
  std::string GetOperatorStr (int consIdx) const ;
  void SetOperator (int consIdx, int val) ;
  double GetCoef (int consIdx, int variIdx) const ;
  void SetCoef (int consIdx, int variIdx, double val) ;
  bool IsEmpty () const ; 
  bool IsMinimized () const ;
  void PrintActiveIdx () const ;
  void Print () const ;
  void PrintConstraint (int idx) const ;
  void SetWitnessRay(int idx, const Vector& rayDirect) ;
  void SetWitnessRay(int consIdx, int rayIdx) ;
  std::vector<Point> GetWitness () ;

  // inline functions 
  const Matrix& get_coefficients () const {
    return _coefficients;
  }
  const Vector& get_constants() const {
    return _constants;
  }
  char GetConstraintState (int idx) const {
    return _active_table[idx] ;
  } 
  void Activate (int consIdx) {
#ifdef VERIMAG_POLYHEDRA_MINIMIZE_OPENMP
#pragma omp atomic write
#endif
    _active_table[consIdx] = IRREDUNDANT ;
  }
  void Deactivate (int consIdx) {
#ifdef VERIMAG_POLYHEDRA_MINIMIZE_OPENMP
#pragma omp atomic write
#endif
    _active_table[consIdx] = REDUNDANT ;
  }
private:
  Matrix _coefficients ;
  Vector _constants ;
  std::vector<int> _operators ;
  int _constraint_num ;
  int _variable_num ;
  int _redundant_num ;
  int _zero_num ;
  int _generator_num ;
  int _id ; 
  Point _central_point ;
  std::vector<char> _active_table ;
  bool _is_minimized ;
  // when the ray is in the direction of a constraint, store
  // the index of the constraint
  std::map<int, int> _witness_ray1 ;
  // for the irredundant constraints found in Determine(), store
  // the ray
  Matrix _witness_ray2 ;
  std::vector<Point> _witness_point ;
} ;

#endif
