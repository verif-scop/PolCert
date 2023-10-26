/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include <iostream>
#include "raytracing.h"
#include "glpkInterface.h"
#include "double.h"

Raytracing::Raytracing (Polyhedron& poly, const Point& point) { 
  if ( poly.IsEmpty() ) {
    std::cerr << "Cannot create raytracing. The polyhedron is empty."
      << std::endl ;
    std::terminate() ;
  }
  if ( point.IsEmpty() ) {
    std::cerr << "Cannot create raytracing. The start point is empty."
      << std::endl ;
    std::terminate() ;
  }

  _polyptr = &poly ;
  _start_point = &point ; 
  _evaluate = poly.get_constants() - poly.get_coefficients() * point.get_coordinates();
  _hasInclusion = true ;
}  

/*******************************************************************************
 * Determine() is the second step of examining the redundancy of constraints.
 * It checks the undetermined constraints until all constraints are determined 
 * as irredundant or redundant. 
 * If any constraint cannot be determied the program aborts. 
 * @para checkInclusion is true if Determin() is called for check inclusion
 * @para startIdx the index of the first constraint of P2, if we are checking
 * if P1 is included in P2
*******************************************************************************/
void Raytracing::Determine (const bool checkInclusion, const int startIdx) {  
  if (checkInclusion && !_hasInclusion) {
    return ;
  }
  
#ifdef VERIMAG_POLYHEDRA_MINIMIZE_OPENMP
#pragma omp parallel for schedule(dynamic)
#endif
#ifdef VERIMAG_POLYHEDRA_MINIMIZE_CILK
  _Cilk_for
#else
  for
#endif
    (int i = 0; i < (int)_undetermined.size(); ++ i) {
    if (! (checkInclusion && !_hasInclusion)) {
      int currIdx = _undetermined.at(i) ;
      if (! (checkInclusion && currIdx < startIdx)) {
	std::vector<int> headIdx ;
	headIdx.push_back(currIdx) ;
	for (int i = 0; i < (int)_intersectHead[currIdx].size(); ++ i) {
	  if (_intersectHead[currIdx].at(i) != currIdx) {
	    headIdx.push_back( _intersectHead[currIdx].at(i) ) ;
	  }
	}
	bool isRedundant = CheckRedundant(currIdx, headIdx) ;
	if(!isRedundant) {
	  if (checkInclusion) {
	    _hasInclusion = false ;
#if !defined(VERIMAG_POLYHEDRA_MINIMIZE_OPENMP) && !defined(VERIMAG_POLYHEDRA_MINIMIZE_CILK)
	    return ;
#endif
	  }
	  _polyptr->Activate(currIdx) ;
	}
      }
    }
  }
}

/*******************************************************************************
 * GetIntersections() computes the distance between the start point and each 
 * intersection of a ray and the constraints. It stores the index of constraints
 * which are nearest to the start point.
 * @para cuurIdx the index of the constraint which is orthogonal to the ray. We
 * assume it is nearest one to the start point at first.
 * @para ray the ray which provides the direction.
 * @return a list of index of constraints, which are nearest to the start point. 
*******************************************************************************/
std::vector<int> Raytracing::GetIntersections (const Ray& ray) {
  std::vector<int> head ;
  double maxVal = 0 ;  
  int consNum = _polyptr->get_constraint_num() ;
  Vector products = _polyptr -> get_coefficients() * ray.get_direction();
  for (int i = 0; i < consNum; ++ i) {
    double consDirect = products(i);
    if ( Double::IsLessEq(consDirect, 0.0) ) continue ;

    double currDistance = GetDistance(i, consDirect) ;
    if ( Double::AreEqual(currDistance, maxVal) ) {
      head.push_back(i) ;
    }
    else if ( Double::IsLessThan(maxVal, currDistance) ) {
      head.clear() ;
      head.push_back(i) ;
      maxVal = currDistance ;
    }
  }

  return head ;
}

/*******************************************************************************
 * GetDistance() computes the distance between a point to a constraint in the 
 * direction of a ray. We compute the multiplicative inverse of the distance
 * to avoid dividing by 0.
 * @para currIdx the index of the constraint to compute
 * @para ray the ray which provides the direction
 * @return the multiplicative inverse of the distance 
*******************************************************************************/
double Raytracing::GetDistance (const int currIdx, const double consDirect) {
  double temp1 = _evaluate(currIdx) ; 
  double res = consDirect / temp1 ;
  return res ;
}

/*******************************************************************************
 * CheckRedundant() checks each undetermined constraint, and determine if the 
 * constraint is redundant.
 * @para currIdx the constraint to determine
 * @para headIdx the list of index of constraints which are nearest to the 
 * start point in the direction of the ray orthogonal to the constraint currIdx. 
 * @return ture if the constraint is redundant.
*******************************************************************************/
bool Raytracing::CheckRedundant (const int currIdx, const std::vector<int>& headIdx) {
  GlpkInterface glpkinter ;
  std::vector<int> currHeadIdx(headIdx) ;
  // the loop has an upper bound which is the number of the constraints
  int consNum = _polyptr->get_constraint_num() ;
  for (int i = 0; i < consNum; ++ i) {
    Point newPoint = glpkinter.GetSatPoint(currHeadIdx, *_polyptr) ;    
    if (newPoint.IsEmpty()) {
      return true ;
    }
    Ray currRay(newPoint, *_start_point) ;
    std::vector<int> currInter = GetIntersections(currRay) ;
    if (currInter.size() == 1 && currInter[0] == currIdx) {
      _polyptr->SetWitnessRay( currIdx, currRay.get_direction() ) ;
      return false ;
    }
    else {
      currHeadIdx.clear() ;
      for (int i = 0; i < (int)currInter.size(); ++ i) {
        if (currInter[i] != currIdx) {
          currHeadIdx.push_back(currInter[i]) ;
        }
      }
    }
  }
  std::cerr << "Error: cannot determine the current constraint" << std::endl ;
  std::terminate() ;
}

/*******************************************************************************
 * The same with RayHitting(), but computes the intersections with matrix 
 * instead of loops and it detect in two directions. 
 * @para checkInclusion is true if Determin() is called for check inclusion
 * @para startIdx the index of the first constraint of P2, if we are checking
 * if P1 is included in P2
********************************************************************************/
void Raytracing::RayHittingMatrixTwoDir (const bool checkInclusion, const int startIdx) {
  const int consNum = _polyptr->get_constraint_num() ;
  Matrix rayMatrix = _polyptr->get_coefficients().transpose() ;
  Matrix normMatrix = _polyptr->get_coefficients() * rayMatrix ;
  for (int i = 0 ; i < consNum; ++ i) {
    rayMatrix.col(i).normalize() ; 
    // set coefficients of duplicated constraints as 0
    if (_polyptr->GetConstraintState(i) == 2) {
      normMatrix.row(i).setZero() ;
    }
  } 
  Matrix evaMatrix = _evaluate.rowwise().replicate(consNum) ; 
  Matrix distanceMatrix = normMatrix.cwiseQuotient(evaMatrix) ; 
  // the result in the form of 
  //      r1     r2   ....   rn
  // c1  res11  res12       res1n
  // ...
  // cn  resn1              resnn                 
  // we need to find the minimum positive value of each column 
  // To simplify the computation, we store 1/distance, which means
  // we will find the maximum value in each column
  std::vector< std::vector<int> > idxList =  GetMaxMinCoefIdx(distanceMatrix, checkInclusion, startIdx) ;
  
  if(checkInclusion == true && _hasInclusion == false) {
    return ;
  }
  
  for (int i = 0; i < (int)idxList.size(); ++ i) {
    _intersectHead[i] = idxList[i] ;
  }
  // push from the last ones for checking inclusion
  for (int i = consNum-1; i >= 0; -- i) {
    if ( _polyptr->GetConstraintState(i) == REDUNDANT) {
      _undetermined.push_back(i) ;
    }
  }
}

/*******************************************************************************
 * Gets the maximum value of each column, and return the coressponding index of
 * the constraints which to be activated. Gets the minimum value of each column, and 
 * activate the coressponding constraints.
 * @para matrix the distance matrix getten from RayHittingMatrix() 
 * @para checkInclusion is true if Determin() is called for check inclusion
 * @para startIdx the index of the first constraint of P2, if we are checking
 * if P1 is included in P2
 * @return the index of the nearest constraint if it is the single nearest one
********************************************************************************/
std::vector< std::vector<int> > Raytracing::GetMaxMinCoefIdx (const Matrix& matrix, const bool checkInclusion, const int startIdx) {
  std::vector< std::vector<int> > idxList ;
  for (int j = 0; j < matrix.cols(); ++ j) {
    double maxVal = 0 ;
    double minVal = 0 ;
    double minIdx = -1 ;
    std::vector<int> idx ;
    for (int i = 0; i < matrix.rows(); ++ i) {
      double currVal = matrix(i, j) ;
      if ( Double::IsLessThan(currVal, 0.0) ) {
        if ( Double::IsLessThan(currVal, minVal) ) {
          minVal = currVal ;
          minIdx = i ;
        }
        else if ( Double::AreEqual(currVal, minVal) ) {
          minIdx = -1 ;
        }
      }
      else if ( ! Double::AreEqual(currVal, 0.0) ) {
        if ( Double::IsLessThan(maxVal, currVal) ) {
          idx.clear() ;
          idx.push_back(i) ;
          maxVal = currVal ;
        }
        else if ( Double::AreEqual(currVal, maxVal) ) {
          idx.push_back(i) ;
        }
      }
    }
    idxList.push_back(idx) ;
    if (idx.size() == 1) { 
      if (checkInclusion == true && idx[0] >= startIdx) {
        _hasInclusion = false ;
        return idxList ;
      }
      _polyptr->SetWitnessRay(idx[0], j) ; 
      _polyptr->Activate( idx[0] ) ;
    }
    if (minIdx != -1) {
      if (checkInclusion == true && minIdx >= startIdx) {
        _hasInclusion = false ;
        return idxList ;
      }
      _polyptr->SetWitnessRay(minIdx, j) ; 
      _polyptr->Activate(minIdx) ;
    } 
  } 
  
  return idxList ;  
}

bool Raytracing::HasInclusion () const {
  return _hasInclusion ;
}
