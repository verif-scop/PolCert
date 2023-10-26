/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include <iostream>
#include <utility>
#include <random>
#include "raytracing.h"
#include "double.h"
#include "glpkInterface.h"

Polyhedron::Polyhedron (int consNum, int variNum) 
  : _constraint_num(consNum), _variable_num(variNum), _is_minimized(false) {
  _coefficients = Matrix::Zero(consNum, variNum) ;
  _constants = Vector::Zero(consNum) ;
  _active_table.resize(consNum, REDUNDANT) ;
  _operators.resize(consNum) ;
  _witness_ray2.resize(variNum, consNum) ;
}

/*******************************************************************************
 * Set the polyhedron to initial state. You can reset the constraints, but the
 * original ones will not be delete.
*******************************************************************************/
void Polyhedron::Init () {
  _is_minimized = false ;
  _active_table.clear() ;
  _active_table.resize(_constraint_num, REDUNDANT) ;  
  _central_point.Clear() ;
  _witness_ray1.clear() ;
  _witness_point.clear() ;
}

/*******************************************************************************
 * Calls the raytracing method to eliminate the redundant constraints, and sets
 * the corresponding value in _active_table as false
 * @return true if minimize successful
*******************************************************************************/
bool Polyhedron::Minimize () {
  GetDuplicateIdx() ; 
  if ( IsEmpty() ) {
    std::cerr << "Minimization failed. The polyhedron is empty." << std::endl ;
    std::terminate() ;
  }
  if (_is_minimized) {
    return true ;
  }
  if ( _central_point.IsEmpty() ) {
    set_central_point( GlpkInterface::GetCentralPoint(*this) ) ;
    // set_central_point( ClpInterface::GetCentralPoint(*this) ) ;
    if(_central_point.IsEmpty()) {
      std::cerr << "Minimization failed. Cannot find a point inside the polyhedra" << std::endl ;
      return false ;
    }
  }
  Raytracing raytrace(*this, _central_point) ;
  raytrace.RayHittingMatrixTwoDir() ; 
  raytrace.Determine() ;
  _is_minimized = true ;
  return true ;
}

/*******************************************************************************
 * Minimization without raytracing.
*******************************************************************************/
void Polyhedron::MinimizeSimple () {
  GetDuplicateIdx() ;
  std::vector<bool> res(_constraint_num) ;
  // #pragma omp parallel for
  for (int i = 0; i < _constraint_num; ++ i) {
    if (_active_table[i] == DUPLICATED) continue ;
    res[i] = GlpkInterface::Sat(*this, i) ;
    if (res[i] == true) {
      Activate(i) ;       
    }
  }  

  _is_minimized = true ;
}

/*******************************************************************************
 * Gets the minimized polyhedron. If the polyhedron is not minimized, minimize
 * it first.
 * @return the minimized polyhedron
*******************************************************************************/
Polyhedron Polyhedron::GetMinimizedPoly () {
  if (! _is_minimized) {
    Minimize() ;
  }
  std::vector<int> indexVec = GetActiveIdx() ; 
  Polyhedron miniPoly = GetSubPoly(indexVec) ;

  return miniPoly ;
}

/*******************************************************************************
 * Creates a polyhedron which contains a subset of constraints of the current
 * polyhedron.
 * @para index the index of the constraints in the subset
 * @return the new polyhedron contains the subset of constraints 
*******************************************************************************/
Polyhedron Polyhedron::GetSubPoly (const std::vector<int>& indexVec) {
  int consNum = indexVec.size() ;
  int variNum = get_variable_num() ;
  Polyhedron newPoly(consNum, variNum) ;
  int currIdx ;
  for (int i = 0; i < consNum; ++ i) {
    currIdx = indexVec[i] ;
    for (int j = 0; j < variNum; ++ j) {
      newPoly.SetCoef( i, j, GetCoef(currIdx, j) ) ;
    }
    newPoly.SetConstant( i, GetConstant(currIdx) ) ;
  }
  return newPoly ;
}

/*******************************************************************************
 * Checks inclusion with raytracing. 
 * For example we check if p1 is included in P2, we need three steps:
 * 1) Check where is the inner point x of P1. If x is not inside P2, then P1
 * is NOT included in P2; 
 * 2) Check each constraint in P2. If any constraint in P2 is irredundant wrt P1
 * then P1 is not included in P2;
 * 3) If no constraint in P2 is irredundant wrt P1 then P1 is included in P2.
 * Note that P1 and P2 should be minimized.
 * @para poly the polyhedron which may be included in the current one, i.e. here
 * we check if poly is included in *this.
 * @return true if poly is included in the current polyhedron 
*******************************************************************************/
bool Polyhedron::Include (const Polyhedron& poly) {
  if ( get_variable_num() != poly.get_variable_num() ) {
    std::cerr << "Caonnt check inclusion. Polyhedra are not in the same environment." 
      << std::endl ;
    std::terminate() ;
  }
  const int consNumP1 = poly.get_constraint_num() ;
  const int consNumP2 = get_constraint_num() ;
  // check if x is inside P2
  for (int i = 0; i < consNumP2; ++ i) {
    if (Satisfy(poly.get_central_point(), i) == false) {
      return false ;
    }
  } 
  // No need to remove duplicated constraints here, 
  // as duplicate constraints are treated as redundant 
  Polyhedron newPoly = Combine(poly) ;
  // Need to use the central point of the new polyhedron to do raytracing, otherwise
  // the central point may be too closed to some constraints and cause raytracing
  // cannot determine if the constraints are redundant.
  newPoly.set_central_point( GlpkInterface::GetCentralPoint(newPoly) ) ;
  if(newPoly._central_point.IsEmpty()) {
    std::cerr << "Cannot check inclusion. Cannot find a point inside the polyhedra" << std::endl ;
    std::terminate() ;
  }
  Raytracing raytrace( newPoly, newPoly._central_point ) ;
  // check constraints of P2  
  raytrace.RayHittingMatrixTwoDir(true, consNumP1) ;    
  if (raytrace.HasInclusion() == false) {
    return false ;
  }
  raytrace.Determine(true, consNumP1) ;
  if (raytrace.HasInclusion() == false) {
    return false ;
  }

  return true ;
}

/*******************************************************************************
 * Put constraints in two polyhedra together in a new polyhedron. The polyhedron
 * at the parameter is put at the beginning.
 * @para poly the polyhedron to be put at the beginning
 * @return the new polyhedron contains all constraints 
*******************************************************************************/
Polyhedron Polyhedron::Combine (const Polyhedron& poly) {
  int consNum1 = poly.get_constraint_num() ;
  int consNum2 = get_constraint_num() ;
  int variNum = get_variable_num() ;
  Polyhedron newPoly(consNum1+consNum2, variNum) ;
  for (int i = 0; i < consNum1; ++ i) {
    for (int j = 0; j < variNum; ++ j) {
      newPoly.SetCoef( i, j, poly.GetCoef(i,j) ) ;
    }
    newPoly.SetConstant( i, poly.GetConstant(i) ) ;
  }
  for (int i = 0; i < consNum2; ++ i) {
    for (int j = 0; j < variNum; ++ j) {
      newPoly.SetCoef( consNum1+i, j, GetCoef(i,j) ) ;
    }
    newPoly.SetConstant( consNum1+i, GetConstant(i) ) ;
  }

  return newPoly ;
}

/*******************************************************************************
 * Checks if a constraint satisfy a point.
 * @para point the point to be satisfied 
 * @para index the index of the constraint to be checked
 * @return true if the constraint satisfy the point
*******************************************************************************/
bool Polyhedron::Satisfy (const Point& point, int index) {
  double res = point.get_coordinates().dot(get_coefficients().row(index) ) ; 
  if ( Double::IsLessEq(res, GetConstant(index)) ) {
    return true ;
  }
  return false ;
}

/*******************************************************************************
 * Gets the index of duplicated constriants and set the corresponding index
 * in _active_table as 2.
*******************************************************************************/
void Polyhedron::GetDuplicateIdx () {
  bool dup = false ;
  for (int i = 1; i < _constraint_num; ++ i) {
    for (int k = i-1; k >= 0; -- k) {
      dup = ConstraintsEq(i, k) ;
      if (dup == true) {
        _active_table[i] = DUPLICATED ;
        break ;
      }
    }
  }
}

/*******************************************************************************
 * @para idx1 the index of the first constraint
 * @para idx2 the index of the second constraint
 * @return true if two constraints are equal
*******************************************************************************/
bool Polyhedron::ConstraintsEq (int idx1, int idx2) {
  int variIdx2 = -1 ;
  // find the first not zero coefficient
  for (int j = 0; j < _variable_num; ++ j) {
    if (variIdx2 == -1 && _coefficients(idx2, j) != 0) {
      variIdx2 = j ;
      break ;
    }
  }
  double temp12 = _coefficients(idx1, variIdx2) ; // may be zero
  double temp22 = _coefficients(idx2, variIdx2) ; // not zero
  // double check
  double lamda = temp12 / temp22 ; 
  for (int j = 0; j < _variable_num; ++ j) {
    if (! Double::AreEqual(_coefficients(idx1, j), _coefficients(idx2, j) * lamda) ) {
      return false ;
    }
  }
  if (! Double::AreEqual( _constants(idx1), _constants(idx2) * lamda) ) {
    return false ;
  }

  return true ;
}

int Polyhedron::get_variable_num () const {
  return _variable_num ;
}
void Polyhedron::set_variable_num (int num) {
  _variable_num = num ;
}

int Polyhedron::get_constraint_num () const {
  return _constraint_num ;
}
void Polyhedron::set_constraint_num (int num) {
  _constraint_num = num ;  
}

int Polyhedron::get_redundant_num () const {
  return _redundant_num ;
}
void Polyhedron::set_redundant_num (int num) {
  _redundant_num = num ;
} 

int Polyhedron::get_zero_num () const {
  return _zero_num ;
}
void Polyhedron::set_zero_num (int num) {
  _zero_num = num ;
} 

int Polyhedron::get_generator_num () const {
  return _generator_num ;
}
void Polyhedron::set_generator_num (int num) {
  _generator_num = num ;
} 

int Polyhedron::get_id () const {
  return _id ;
}
void Polyhedron::set_id (int id) {
  _id = id ;
}

std::vector<int> Polyhedron::GetActiveIdx () {
  std::vector<int> idxVec ;
  for (int i = 0; i < (int)_active_table.size(); ++ i) {
    if (_active_table[i] == IRREDUNDANT) {
      idxVec.push_back(i) ; 
    } 
  }
  return idxVec ;
}

std::vector<int> Polyhedron::GetInactiveIdx () {
  std::vector<int> idxVec ;
  for (int i = 0; i < (int)_active_table.size(); ++ i) {
    if (_active_table[i] != IRREDUNDANT) {
      idxVec.push_back(i) ; 
    } 
  }
  return idxVec ;
}

/*******************************************************************************
 * _active_table[i] is 2 if the constraint i is duplicated, 1 if it is 
 * irredundant, 0 if it is redundant but not duplicated.
 * @return true if the constrinat is irredundant
 * Note: this functions may be not thread safe
*******************************************************************************/
bool Polyhedron::IsActive (int consIdx) const {
  bool ret ;
  if (_active_table[consIdx] == IRREDUNDANT) {
    ret = true ;
  }
  else
  {
    ret = false ;
  }
  return ret ;
}

void Polyhedron::set_central_point(const Point& point) {
  _central_point = point ;
}

Point Polyhedron::get_central_point () const {
  return _central_point ;
}

Vector Polyhedron::GetConstraint (int consIdx) const {
  return _coefficients.row(consIdx) ;
}
 
void Polyhedron::SetConstraint (int consIdx, const Vector& cons) {
  _coefficients.row(consIdx) = cons ;
}

double Polyhedron::GetConstant (int consIdx) const {
  return _constants(consIdx) ;
} 

void Polyhedron::SetConstant (int consIdx, double val) {
  _constants(consIdx) = val ;
}

int Polyhedron::GetOperator (int consIdx) const {
  return _operators[consIdx] ;
}

std::string Polyhedron::GetOperatorStr (int consIdx) const {
  int op = _operators[consIdx] ;
  if (op == 0) return "<" ;
  else if (op == 1) return "<=" ;
  else if (op == 2) return "=" ;
  else return "" ;
}

void Polyhedron::SetOperator (int consIdx, int val) {
  _operators[consIdx] = val ;
}

double Polyhedron::GetCoef (int consIdx, int variIdx) const {
  return _coefficients(consIdx, variIdx) ;
}

void Polyhedron::SetCoef (int consIdx, int variIdx, double val) {
  _coefficients(consIdx, variIdx) = val ;
}


/*******************************************************************************
 * @return true if the polyhedron is empty
*******************************************************************************/
bool Polyhedron::IsEmpty () const {
  if (_coefficients.size() == 0)
    return true ;
  return false ;
}
  
/*******************************************************************************
 * @return true if the polyhedron is minimized
*******************************************************************************/
bool Polyhedron::IsMinimized () const {
  return _is_minimized ;
}

/*******************************************************************************
 * Prints the index of the avtivate constraints
*******************************************************************************/
void Polyhedron::PrintActiveIdx () const {
  std::cout<< "The index of the activate constraints are: " << std::endl ;
  for (int i = 0; i < (int)_active_table.size(); ++ i) {
    if (_active_table[i] == IRREDUNDANT) {
      std::cout << i << " " ;
    } 
  }
  std::cout << std::endl ;
}

/*******************************************************************************
 * Prints the constraints to the terminal
*******************************************************************************/
void Polyhedron::Print () const {
  std::cout << "The constraints are (in form [coefficients <op> constant]):" << std::endl ;
  std::cout << "Begin" << std::endl ;
  for (int i = 0; i < _constraint_num; ++ i) {
    for (int j = 0; j < _variable_num; ++ j) {
      std::cout << _coefficients(i, j) << " " ;
    }
    std::cout << " " << GetOperatorStr(i) << " " << _constants[i] << std::endl ;
  }
  std::cout << "End" << std::endl ;
}

/*******************************************************************************
 * Prints the {idx}th constraint to the terminal
*******************************************************************************/
void Polyhedron::PrintConstraint (int idx) const {
  std::cout << get_coefficients().row(idx) << " "
    << GetConstant(idx) << std::endl ;
}

/*******************************************************************************
 * Set a ray for the corresponding constraint. 
 * @para i the index of the constraint.
 * @para rayDirect the ray direction
*******************************************************************************/
void Polyhedron::SetWitnessRay(int consIdx, int rayIdx) {
  _witness_ray1.insert( std::pair<int, int>(consIdx, rayIdx) ) ;
}

void Polyhedron::SetWitnessRay(int idx, const Vector& rayDirect) {
  _witness_ray2.col(idx) = rayDirect ;
}

/*******************************************************************************
 * Compute the witness points if it has not been computed, otherwise return
 * the witness points.
*******************************************************************************/
std::vector<Point> Polyhedron::GetWitness () {
  if ( ! _witness_point.empty() ) {
    return _witness_point ;
  } 
  if ( ! IsMinimized() ) {
    Minimize() ;
  }
  std::vector<int> activeVec = GetActiveIdx() ; 
  int consNum = activeVec.size() ;
  Matrix rayMatrix(get_variable_num(), consNum) ;
  Matrix consMatrix( consNum, get_variable_num() ) ;
  Vector constantVec( consNum ) ;
  for (int i = 0; i < consNum; ++ i) {
    int currIdx = activeVec[i] ;
    consMatrix.row(i) = get_coefficients().row(currIdx) ;
    constantVec(i) = GetConstant(currIdx) ;
    auto it1 = _witness_ray1.find(currIdx) ; 
    if ( it1 != _witness_ray1.end() ) {
      double res = get_coefficients().row(currIdx) 
        * _coefficients.row(it1->second).transpose() ; 
      // for two direction ray
      if ( Double::IsLessThan(res, 0.0) ) {
        rayMatrix.col(i) = -get_coefficients().row(it1->second) ; 
      }  
      else {
        rayMatrix.col(i) = get_coefficients().row(it1->second) ; 
      }
      rayMatrix.col(i).normalize() ;
    }
    else {  
      rayMatrix.col(i) = std::move( _witness_ray2.col(currIdx) ) ;
    }
  }
  Matrix normMatrix = consMatrix * rayMatrix ;
  Vector evaluate = constantVec - 
    consMatrix * get_central_point().get_coordinates() ;
  Matrix evaMatrix = evaluate.rowwise().replicate(consNum) ; 
  Matrix distanceMatrix = normMatrix.cwiseQuotient(evaMatrix) ; 

  for (int j = 0; j < distanceMatrix.cols(); ++ j) {
    double maxVal = -1 ;
    double sndMaxVal = -1 ; 
    int maxIdx = -1 ;
    double currVal ;
    for (int i = 0; i < distanceMatrix.rows(); ++ i) {
      currVal = distanceMatrix(i, j) ;
      if ( Double::IsLessThan(0.0, currVal) ) {
        if ( Double::IsLessThan(maxVal, currVal) ) {
          maxVal = currVal ;
          maxIdx = i ;
        }
      }
    }
    for (int i = 0; i < distanceMatrix.rows(); ++ i) {
      if (i == maxIdx) continue ; 
      currVal = distanceMatrix(i, j) ;
      if ( Double::IsLessThan(0.0, currVal) ) {
        if ( Double::IsLessThan(sndMaxVal, currVal) ) {
          sndMaxVal = currVal ;
        }
      }
    }
    // the witness point is at: central_point + distance * direction
    Vector witness ;
    if ( Double::AreEqual(sndMaxVal, -1.0) ) {
      // did't meet a second constraint, use distant to the constraint + 1 
      witness = get_central_point().get_coordinates() 
        + (1 / maxVal + 1) * rayMatrix.col(j) ; 
    }
    else {
      // the middle of first and second met constraint 
      witness = get_central_point().get_coordinates() 
        + ( (1 / maxVal + 1 / sndMaxVal) / 2 ) * rayMatrix.col(j) ;
    }
    _witness_point.push_back( Point(witness) ) ;
  }

  return _witness_point ;
}
