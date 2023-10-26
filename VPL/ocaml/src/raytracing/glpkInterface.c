/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include "glpkInterface.h"

GlpkInterface::GlpkInterface () 
  : _epsilon(0.1) {
  _glp = glp_create_prob() ;
}

GlpkInterface::~GlpkInterface () { 
  glp_delete_prob(_glp) ;
}

/*******************************************************************************
 * Call simplex method in GLPK and compute the central point of the polyhedron
 * @para poly the given polyhedron
 * @return the central point  
*******************************************************************************/
Point GlpkInterface::GetCentralPoint (const Polyhedron& poly) {
  GlpkInterface glpkinter ;
  glp_set_obj_dir(glpkinter._glp, GLP_MIN) ;
  int consNum = poly.get_constraint_num() ;
  int variNum = poly.get_variable_num() ;
  glp_add_rows(glpkinter._glp, 2*consNum) ; 
  // the constraints: ax <= b
  // ||ax - b|| / ||a|| >= r1  =>  ax + ||a||r1 <= b 
  // ||ax - b|| / ||a|| <= r2  =>  ax + ||a||r2 >= b
  // 0.1 <= r1 <= r2
  // index starts from 1, there are 2*consNum constraints
  for(int i = 0; i < consNum; ++ i) {
    double constant = poly.GetConstant(i) ;
    glp_set_row_bnds(glpkinter._glp, 2*i+1, GLP_UP, 0.0, constant) ;
    glp_set_row_bnds(glpkinter._glp, 2*i+2, GLP_LO, constant, 0.0) ;  
  } 
  // there are two new column for r1 and r2
  glp_add_cols(glpkinter._glp, variNum+2) ;
  for(int j = 1; j < variNum+1; ++ j) {
    glp_set_col_bnds(glpkinter._glp, j, GLP_FR, 0.0, 0.0) ;
  }
  glp_set_col_bnds(glpkinter._glp, variNum+1, GLP_LO, 0.1, 0.0) ;
  glp_set_col_bnds(glpkinter._glp, variNum+2, GLP_LO, 0.1, 0.0) ;
  // obj = r2 - r1
  glp_set_obj_coef(glpkinter._glp, variNum+1, -1.0) ;
  glp_set_obj_coef(glpkinter._glp, variNum+2, 1.0) ;
  int valNum = 2 * consNum * (variNum + 2) ;
  int* idxi = new int[valNum+1] ;
  int* idxj = new int[valNum+1] ;
  double* vals = new double[valNum+1] ;
  int idx = 1 ;
  for(int i = 0; i < consNum; ++ i) {
    for(int j = 0; j < variNum; ++ j) {
      idxi[idx] = 2 * i + 1 ;
      idxj[idx] = j + 1 ;
      vals[idx] = poly.GetCoef(i, j) ;
      ++ idx ;
      idxi[idx] = 2 * i + 2 ;
      idxj[idx] = j + 1 ;
      vals[idx] = poly.GetCoef(i, j) ;
      ++ idx ;
    }
  } 
  for(int i = 0; i < consNum; ++ i) {
    double currNorm = poly.get_coefficients().row(i).norm() ;
    idxi[idx] = 2 * i + 1 ;
    idxj[idx] = variNum + 1 ;
    vals[idx] = currNorm ;
    ++ idx ;
    idxi[idx] = 2 * i + 1 ;
    idxj[idx] = variNum + 2 ;
    vals[idx] = 0 ;
    ++ idx ;
    idxi[idx] = 2 * i + 2 ;
    idxj[idx] = variNum + 1 ;
    vals[idx] = 0 ;
    ++ idx ;
    idxi[idx] = 2 * i + 2 ;
    idxj[idx] = variNum + 2 ;
    vals[idx] = currNorm ;
    ++ idx ;
  }
  glp_load_matrix(glpkinter._glp, valNum, idxi, idxj, vals) ;
  glp_smcp para ;
  glp_init_smcp(&para) ;
  para.msg_lev = GLP_MSG_OFF ;
  glp_simplex(glpkinter._glp, &para) ;
  Point point ;
  if (glp_get_prim_stat(glpkinter._glp) == GLP_FEAS) {
    Vector coord(variNum) ;
    for(int j = 0; j < variNum; ++ j) {
      coord(j) = glp_get_col_prim(glpkinter._glp, j+1) ;
    } 
    point.set_coordinates(coord) ;
  }

  delete[] idxi ;
  delete[] idxj ;
  delete[] vals ;
  return point ;
}

/*******************************************************************************
 * Calls simplex method in GLPK and compute a satisfied point, i.e. this point
 * satisfy all the constraints of the polyhedron
 * @para headIdx the index of constraints which are met by the ray first
 * @para poly the given polyhedron
 * @return the satisfied point  
*******************************************************************************/
Point GlpkInterface::GetSatPoint (const std::vector<int>& headIdx, const Polyhedron& poly) {
  int consNum = headIdx.size() ;
  int variNum = poly.get_variable_num() ;
  int oriConsNum = glp_get_num_rows(_glp) ;
  glp_add_rows(_glp, consNum) ; 
  double constant ;
  for(int i = 0; i < consNum; ++ i) {
    constant = poly.GetConstant( headIdx[i] ) ;
    // minus _epsilon for getting a point inside the polyhedron
    if (oriConsNum + i == 0) {
      // the first constraint is Ax >= b + epsilon, others are Ax <= b - epsilon
      glp_set_row_bnds(_glp, 1, GLP_LO, constant+_epsilon, 0.0) ;
    }
    else {
      glp_set_row_bnds(_glp, oriConsNum+i+1, GLP_UP, 0.0, constant-_epsilon) ;
    }
  }
  int* idxj = new int[variNum+1] ;
  double* vals = new double[variNum+1] ;
  if (oriConsNum == 0) {
    glp_set_obj_dir(_glp, GLP_MIN) ;
    glp_add_cols(_glp, variNum) ;
    for(int j = 1; j < variNum+1; ++ j) {
      glp_set_col_bnds(_glp, j, GLP_FR, 0.0, 0.0) ;
    }
    // set the object as 0 to avoid the optimization phase
    glp_set_obj_coef(_glp, 1, 0.0) ; 
  } 
  for(int i = 0; i < consNum; ++ i) {
    int consIdx = headIdx[i] ;
    for(int j = 0; j < variNum; ++ j) {
      idxj[j+1] = j + 1 ;
      vals[j+1] = poly.GetCoef(consIdx, j) ;
    }
    glp_set_mat_row(_glp, oriConsNum+i+1, variNum, idxj, vals) ;
  } 
  glp_smcp para ;
  glp_init_smcp(&para) ;
  para.msg_lev = GLP_MSG_OFF ;
  glp_simplex(_glp, &para) ;
  Point point ;
  if (glp_get_prim_stat(_glp) == GLP_FEAS) {
    Vector coord(variNum) ;
    for(int j = 0; j < variNum; ++ j) {
      coord(j) = glp_get_col_prim(_glp, j+1) ;
    } 
    point.set_coordinates(coord) ;
  }
 
  delete[] idxj ;
  delete[] vals ;
  return point ;
}


/*******************************************************************************
 * Tests if the {idx}th constraint is redundant.
*******************************************************************************/
bool GlpkInterface::Sat (const Polyhedron& poly, int idx) {
  GlpkInterface glpkinter ;
  int consNum = poly.get_constraint_num() ;
  int variNum = poly.get_variable_num() ;
  glp_add_rows(glpkinter._glp, consNum) ; 
  // the first constraint is Ax >= b + epsilon, others are Ax <= b - epsilon
  double constant ;
  for(int i = 0; i < consNum; ++ i) {
    constant = poly.GetConstant(i) ;
    glp_set_row_bnds(glpkinter._glp, i+1, GLP_UP, 0.0, constant-glpkinter._epsilon) ;
  }
  constant = poly.GetConstant(idx) ;
  glp_set_row_bnds(glpkinter._glp, idx+1, GLP_LO, constant+glpkinter._epsilon, 0.0) ;
  int* idxj = new int[variNum+1] ;
  double* vals = new double[variNum+1] ;
  glp_set_obj_dir(glpkinter._glp, GLP_MIN) ;
  glp_add_cols(glpkinter._glp, variNum) ;
  for(int j = 1; j < variNum+1; ++ j) {
    glp_set_col_bnds(glpkinter._glp, j, GLP_FR, 0.0, 0.0) ;
  }
  // set the object as 0 to avoid the optimization phase
  glp_set_obj_coef(glpkinter._glp, 1, 0.0) ;  
  for(int i = 0; i < consNum; ++ i) {
    for(int j = 0; j < variNum; ++ j) {
      idxj[j+1] = j + 1 ;
      vals[j+1] = poly.GetCoef(i, j) ;
    }
    glp_set_mat_row(glpkinter._glp, i+1, variNum, idxj, vals) ;
  } 
  glp_smcp para ;
  glp_init_smcp(&para) ;
  para.msg_lev = GLP_MSG_OFF ;
  glp_simplex(glpkinter._glp, &para) ;
  bool res ;
  if (glp_get_prim_stat(glpkinter._glp) == GLP_FEAS) {
    res = true ;
  }
  else {
    res = false ;
  }
 
  delete[] idxj ;
  delete[] vals ;
  return res ;
}

/*******************************************************************************
 * Solve LP with a random objective function (now use [1, ..., 1])
 * @para poly the polyhedron to be solved
 * @para obj the objective function
 * @return true if the optimal solution exists 
*******************************************************************************/
bool GlpkInterface::Simplex (const Polyhedron& poly, const VectorZ& obj, int objdir) {
  if (objdir == GLP_MAX) {
    glp_set_obj_dir(_glp, GLP_MAX) ;
  }
  else {
    glp_set_obj_dir(_glp, GLP_MIN) ;
  }
  int consNum = poly.get_constraint_num() ;
  int variNum = poly.get_variable_num() ;
  glp_add_rows(_glp, consNum) ; 
  for(int i = 0; i < consNum; ++ i) {
    double constant = poly.GetConstant(i) ;
    glp_set_row_bnds(_glp, i+1, GLP_UP, 0.0, constant) ;
  } 
  glp_add_cols(_glp, variNum) ;
  for(int j = 0; j < variNum; ++ j) {
    glp_set_col_bnds(_glp, j+1, GLP_FR, 0.0, 0.0) ;
    //glp_set_col_bnds(_glp, j+1, GLP_LO, 0.0, 0.0) ;
    glp_set_obj_coef( _glp, j+1, obj(j) ) ;
  }
  int valNum = consNum * variNum ;
  int* idxi = new int[valNum+1] ;
  int* idxj = new int[valNum+1] ;
  double* vals = new double[valNum+1] ;
  int idx = 1 ;
  for(int i = 0; i < consNum; ++ i) {
    for(int j = 0; j < variNum; ++ j) {
      idxi[idx] = i + 1 ;
      idxj[idx] = j + 1 ;
      vals[idx] = poly.GetCoef(i, j) ;
      ++ idx ;
    }
  } 
  glp_load_matrix(_glp, valNum, idxi, idxj, vals) ;
  glp_smcp para ;
  glp_init_smcp(&para) ;
  para.msg_lev = GLP_MSG_OFF ;
  glp_simplex(_glp, &para) ; 
  Vector point(variNum) ;
  bool result ;
  int state = glp_get_status(_glp) ;
  if (state == GLP_UNBND) {
    result = false ;
  } 
  if (state == GLP_OPT) {
    result = true ;
  }
  delete[] idxi ;
  delete[] idxj ;
  delete[] vals ;
  return result ;
}
  
/*******************************************************************************
 * Gets the basic variable index of rows and non-basic variable index of columns
*******************************************************************************/
void GlpkInterface::GetBasis () {
  int rowNum = glp_get_num_rows(_glp) ; 
  int colNum = glp_get_num_cols(_glp) ; 
  for (int j = 0; j < colNum; ++ j) {
    if (glp_get_col_stat(_glp, j+1) == GLP_BS) {
      _basic_idx.push_back(j) ;
    }
  }
  for (int i = 0; i < rowNum; ++ i) {
    if (glp_get_row_stat(_glp, i+1) == GLP_BS) {
      _basic_idx.push_back(colNum+i) ;
    }
  } 
}

/*******************************************************************************
 * Gets the index of all basic variables
 * x1 x2 ... xn slack1 slack2 ... slackn
*******************************************************************************/
const std::vector<int>& GlpkInterface::get_basic_idx () {
  return _basic_idx ;
}

/*******************************************************************************
 * Gets the index of all nonbasic variables
 * x1 x2 ... xn slack1 slack2 ... slackn
*******************************************************************************/
std::vector<int> GlpkInterface::GetNonbasicIdx () {
  std::vector<int> nonbasic ;
  int rowNum = glp_get_num_rows(_glp) ;
  int colNum = glp_get_num_cols(_glp) ;
  int idx = 0 ;
  for (int i = 0; i < rowNum+colNum; ++ i) {
    if ( i == _basic_idx[idx] ) {
      ++ idx ;
    }
    else {
      nonbasic.push_back(i) ;


    }
  }
  return nonbasic ;
}

/*******************************************************************************
 * Gets the state of variables
 * @para idx the index of variable x1 x2 ... xn slack1 slack2 ... slackn
*******************************************************************************/

int GlpkInterface::GetVariState (int idx) {
  int colNum = glp_get_num_cols(_glp) ;
  int state = -1 ;
  if (idx < colNum) {
    state = glp_get_col_stat(_glp, idx+1) ;
  }
  else {
    state = glp_get_row_stat(_glp, idx-colNum+1) ;
  }
  return state ;
}

