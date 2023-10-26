#include <iostream>
#include <vector>
#include "ioInterface.h"
#include "glpkInterface.h"

extern "C"{
#include <stdio.h>
#include <memory.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
}

extern "C" value new_poly(value n_cons_, value n_var_){
  CAMLparam2(n_cons_, n_var_);
  int n_cons = Int_val(n_cons_);
  int n_var = Int_val(n_var_);
  CAMLreturn((value) (new Polyhedron(n_cons, n_var)));
}

extern "C" value delete_poly(value poly){
  CAMLparam1(poly);
  delete((Polyhedron*) poly);
  CAMLreturn(Val_unit);
}

extern "C" value set_coeff(value poly, value i_cons_, value i_var_, value coeff_){
  CAMLparam4(poly, i_cons_, i_var_, coeff_);
  int i_cons = Int_val(i_cons_);
  int i_var = Int_val(i_var_);
  double coeff = Double_val(coeff_);
  ((Polyhedron*) poly)->SetCoef(i_cons, i_var, coeff);
  CAMLreturn(Val_unit);
}

extern "C" value minimize(value poly){
  CAMLparam1(poly);
  ((Polyhedron*) poly)->Minimize();
  CAMLreturn(Val_unit);
}

extern "C" value is_empty(value poly){
  CAMLparam1(poly);
  CAMLreturn(Val_bool(((Polyhedron*) poly)->IsEmpty()));
}

extern "C" value is_true(value poly, value id_){
  CAMLparam2(poly, id_);
  int id = Int_val(id_);
  std::vector<int> ids = ((Polyhedron*) poly)->GetActiveIdx();
  CAMLreturn(std::find(ids.begin(), ids.end(), id) != ids.end()
	     ? Val_true : Val_false);
}

extern "C" value get_witness_coeff(value poly, value id_, value var_){
  CAMLparam3(poly, id_, var_);
  int id = Int_val(id_);
  int var = Int_val(var_);
  Point p = ((Polyhedron*) poly)->GetWitness()[id];
  double coeff = p.get_coordinates()[var];

  CAMLreturn(caml_copy_double(coeff));
}

extern "C" value set_central_point_coeff(value poly, value var_, value coeff_){
  CAMLparam3(poly, var_, coeff_);
  Polyhedron* poly2 = (Polyhedron*) poly;
  Point p = poly2->get_central_point ();
  int var = Int_val(var_);
  double coeff = Double_val(coeff_);
  if (p.IsEmpty()) {
    int variNum = poly2->get_variable_num() ;
    Vector coord(variNum) ;
    coord(var) = coeff;
    p.set_coordinates(coord);
  } else {
    p.set_coefficient(var, coeff);
  }
  poly2->set_central_point (p);
  CAMLreturn(Val_unit);
}

/*
#include <iostream>
#include <vector>
#include "ioInterface.h"
#include "glpkInterface.h"

extern "C"{
#include <stdio.h>
#include <memory.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
}

extern "C" Polyhedron* new_poly(value n_cons_, value n_var_){
	CAMLparam2(n_cons_, n_var_);
	int n_cons = Int_val(n_cons_);
	int n_var = Int_val(n_var_);
	return new Polyhedron(n_cons, n_var);
}

extern "C" value delete_poly(Polyhedron* poly){
	CAMLparam0();
	delete(poly);
	CAMLreturn(Val_unit);
}

extern "C" value set_coeff(Polyhedron* poly, value i_cons_, value i_var_, value coeff_){
	CAMLparam3(i_cons_, i_var_, coeff_);
	int i_cons = Int_val(i_cons_);
	int i_var = Int_val(i_var_);
	double coeff = Double_val(coeff_);
	poly->SetCoef(i_cons, i_var, coeff);
	CAMLreturn(Val_unit);
}

extern "C" value minimize(Polyhedron* poly){
	CAMLparam0();
	poly->Minimize();
	CAMLreturn(Val_unit);
}

extern "C" value get_true_constraints(Polyhedron* poly){
	CAMLparam0();
	CAMLlocal1(r);

	std::vector<int> ids = poly->GetActiveIdx();
	int* ids_a = &ids[0];
	r = caml_alloc_array(caml_copy_int32, ids_a);
	CAMLreturn (r);
}

extern "C" value is_empty(Polyhedron* poly){
	CAMLparam0();
	CAMLreturn(Val_bool(poly->IsEmpty()));
}

extern "C" value is_true(Polyhedron* poly, value id_){
	CAMLparam1(id_);
	int id = Int_val(id_);
	std::vector<int> ids = poly->GetActiveIdx();
	if(std::find(ids.begin(), ids.end(), id) != ids.end())
		CAMLreturn(Val_bool(true));
	else
		CAMLreturn(Val_bool(false));
}

extern "C" value get_witness_coeff(Polyhedron* poly, value id_, value var_){
	CAMLparam2(id_, var_);
	int id = Int_val(id_);
	int var = Int_val(var_);
	Point p = poly->GetWitness()[id];
	double coeff = p.get_coordinates()[var];
	CAMLreturn(caml_copy_double(coeff));
}

extern "C" value set_central_point_coeff(Polyhedron* poly, value var_, value coeff_){
	CAMLparam2(var_, coeff_);
	Point p = poly->get_central_point ();
	int var = Int_val(var_);
	double coeff = Double_val(coeff_);
	if (p.IsEmpty()){
		int variNum = poly->get_variable_num() ;
		Vector coord = Vector::Zero(variNum) ;
		coord(var) = coeff;
		p.set_coordinates(coord);
	}
	else
		p.set_coefficient(var, coeff);
	poly->set_central_point (p);
	
	CAMLreturn(Val_unit);
}
*/
