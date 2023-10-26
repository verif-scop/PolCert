/*******************************************************************************
 * Copyright (c) 2016 Dec. Verimag. All rights reserved.
 * @author Hang YU
*******************************************************************************/

#include <iostream>
#include <fstream>
#include <regex>
#include <algorithm>
#include "ioInterface.h"

IoInterface::IoInterface () 
  : _poly_num(0), _cons_num(0), _redundant_num(0), _vari_num(0), _zero_num(0)
{}

/*******************************************************************************
 * Read polyhedron from a file. The polyhedron is stored as matrix in that file.
*******************************************************************************/
std::vector<Polyhedron> IoInterface::LoadPolyhedra (const char* filepath) {
  std::vector<Polyhedron> polyVec ;
  std::ifstream ifs(filepath);
  if ( ! ifs.is_open() ) {
    std::cerr << "Cannot open file." << std::endl ;
    std::terminate() ;
  }
  std::string line ;
  std::string infoName ;
  int infoVal ;
  int pos ;
  std::regex pattern("[[:space:]]") ;
  while( std::getline(ifs, line) ) {
    if (line.length() == 0) continue ;
    line = std::regex_replace(line, pattern, "");
    if (line == "begin" || line == "Begin" || line == "BEGIN") break ;
    pos = line.find("=") ;
    infoName = line.substr(0, pos) ;
    infoVal = std::stoi(line.substr(pos+1));
    // tolower is a global function
    std::transform(infoName.begin(), infoName.end(), infoName.begin(), ::tolower);
    if (infoName == "polyhedra") {
      _poly_num = infoVal ;
    }
    if (infoName == "constraints") {
      _cons_num = infoVal ;
    }
    if (infoName == "variables") {
      _vari_num = infoVal ;
    }
    if (infoName == "zeros") {
      _zero_num = infoVal ;
    }
    if (infoName == "redundancy") {
      _redundant_num = infoVal ;
    }
  }

  if (_poly_num == 0 || _cons_num == 0 || _vari_num == 0) {
    std::cerr << "Need information of the number of Polyhedra, constraints and variables" << std::endl ;
    std::terminate() ;
  }

  for (int i = 0; i < _poly_num; ++ i) {
    // read the name of polyhedron
    while( std::getline(ifs, line) ) {
      line = std::regex_replace(line, pattern, "") ;
      if (line[0] >= 'a' && line[0] <= 'z') break ;
      else if (line[0] >= 'A' && line[0] <= 'Z') break ;
      else if (line[0] >= '0' && line[0] <= '9') {
        std::cerr << "The name of Polyhedron is missing or illegal." << std::endl ;
        std::terminate() ;
      }
      else if (line.length() != 0) {
        std::cerr << "The name of Polyhedron is illegal." << std::endl ;
        std::terminate() ;
      }
    }
    // the polyhedra names are in the form: P_N_C_R_V_Z_G_I, 
    // where N: number of polyhdra, C: total number of constraints,
    // R: number of redundant constraints, V: number of variables
    // G: number of generators, I: the identity of polydedron
    Polyhedron newPoly(_cons_num, _vari_num) ;
    std::regex rgx ("_") ; 
    // default constructor: end of sequence
    std::regex_token_iterator<std::string::iterator> end ; 
    std::regex_token_iterator<std::string::iterator> 
      it (line.begin(), line.end(), rgx, -1) ;
    // ignore the information except the number of generator and id
    // TODO: maybe do not need the information of ioInterface class
    for (int p = 0; p < 6; ++ p) {
      ++ it ;
    }
    newPoly.set_generator_num( std::stoi(*it) ) ;
    ++ it ;
    newPoly.set_id( std::stoi(*it) ) ;
    newPoly.set_redundant_num(_redundant_num) ;
    newPoly.set_zero_num(_zero_num) ;
    // read the constraints matrix
    double newVal ;
    for (int i = 0; i < _cons_num; i++) {
      char op = ' ' ;
      for (int j = 0; j < _vari_num; j++) {
        ifs >> newVal ;
        newPoly.SetCoef(i, j, newVal) ;
      }
      // read the operators begin
      while (op == ' ') {
        ifs >> op ;
      }
      // use int to present operators, 0: "<", 1: "<=", 2:"="
      if (op == '=') {
        newPoly.SetOperator(i, 2) ; 
      }
      else if (op == '<') {
        ifs >> op ;
        if (op == '=') {
          newPoly.SetOperator(i, 1) ;
        }
        else {
          newPoly.SetOperator(i, 0) ;
        }
      } 
      // read the operators end
      ifs >> newVal ;
      newPoly.SetConstant(i, newVal) ;
    }
    polyVec.push_back( std::move(newPoly) ) ;
  }

  return polyVec ;
}


int IoInterface::get_poly_num () {
  return _poly_num ;
}

int IoInterface::get_cons_num () {
  return _cons_num ;
}

int IoInterface::get_redundant_num () {
  return _redundant_num ;
}

int IoInterface::get_vari_num () {
  return _vari_num ;
}

int IoInterface::get_zero_num () {
  return _zero_num ;
}
