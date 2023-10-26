let (print_channel : out_channel * string -> unit) = function
	(o,s) -> (output_string o s);;

let str_to_ieq = 
"def to_ieq(poly, ring, variables):
	monomials = [ring(1)] + [ring(x) for x in variables]
	return [poly.monomial_coefficient(m) for m in monomials]
"

let str_projection = 
"#PROJECTION
def standard_basis_vector(n, i):
    assert i>=0
    assert i<n
    return vector(QQ, [0,]*i + [1] + [0,]*(n-i-1))

def monomial_image(m,variables,nb_var):
    try:
        return standard_basis_vector(nb_var,variables.index(str(m)))
    except ValueError:
        return vector(QQ, nb_var)

#Projète le polyèdre suivant la variable
# variables doit contenir la liste des variables, y compris celle qui va être projetée
#P doit avoir la même dimension que variables
def proj(P,variable, variables, ring, nb_dim):
	monomials = [ring(x) for x in variables]
	vertices = P.vertices()
	i = variables.index(variable)
	new_variables = variables[0:i] + variables[i+1:] 
	nb_var = len(variables) -1
	projection = matrix(QQ, [monomial_image(m,new_variables,nb_var) for m in monomials])
	proj_vertices = [(v.vector()*projection)[0:len(new_variables)] for v in vertices]
	return Polyhedron(vertices = proj_vertices)

#On va projeter toutes les variables sauf variable pour obtenir l'intervalle de variable
def get_itv_from_poly(P,variable,variables,ring, nb_dim):
	i = variables.index(variable)
	new_variables = variables[0:i] + variables[i+1:] #on enlève variable de variables
	variables_inter = variables
	for v in new_variables:	#on parcourt toutes les variables sauf variable	
		P = proj(P,v,variables_inter,ring, nb_dim)
		i = variables_inter.index(v)
		variables_inter = variables_inter[0:i] + variables_inter[i+1:]
	vertices = P.vertices_list()
	if len(vertices) == 0:
		return []
	if len(vertices) == 1:
		return [int(vertices[0][0]), int(vertices[0][0])]
	return [int(min(vertices[0][0],vertices[1][0])),int(max(vertices[0][0],vertices[1][0]))]
"

let str_plot_polyhedra = 
"# polyhedra = polyhedron list
def plot_polyhedra(polyhedra, nb_dim):
	if len(polyhedra) > 0:
		if nb_dim == 1:
			couleur = color(polyhedra[0])
			to_plot = polyhedra[0].projection().render_line_1d()
			for i in range(1,len(polyhedra)):
				couleur = color(polyhedra[i])
				to_plot += polyhedra[i].projection().render_line_1d()

		if nb_dim == 2:
			couleur = color(polyhedra[0])
			to_plot = polyhedra[0].projection().render_outline_2d(color = couleur)
			for i in range(1,len(polyhedra)):
				couleur = color(polyhedra[i])
				to_plot += polyhedra[i].projection().render_outline_2d(color = couleur)
				
		if nb_dim == 3:
			couleur = color(polyhedra[0])
			to_plot = polyhedra[0].projection().render_wireframe_3d(color = couleur)
			for i in range(1,len(polyhedra)):
				couleur = color(polyhedra[i])
				to_plot += polyhedra[i].projection().render_wireframe_3d(color = couleur)
		return to_plot
"
let str_plot_polynomial = 
"
def plot_polynomial(f, ranges, parameters):
	var(' '.join(parameters))
	if len(parameters) == 1:
		to_plot = plot(f,ranges[0][0],ranges[0][1])

	if len(parameters) == 2:
		to_plot = plot3d(f,(parameters[0], ranges[0][0],ranges[0][1]),(parameters[1], ranges[1][0],ranges[1][1]), color = 'green', opacity=0.2)
	return to_plot
"

let str_color = 
"#Color handling
colors = []
color_bind = []

def bind_color(x):
	if color_bind.count(x) == 0:
		color_bind.append(x)

def def_colors():
	import random
	random.seed(425)
	r = lambda: random.random()
	for i in range(0,len(color_bind)):
		colors.append((r(),r(),r()))

def color(x):
	return colors[color_bind.index(x)]
"

let str_color_from_polyhedra = 
"#polyhedra : polyhedron list
def color_from_polyhedra(polyhedra):
	for p in polyhedra:
		bind_color(p)
	def_colors()
"

let str_plot_regions =
"def plot_regions(regions, nb_dim):
	if len(regions) > 0:
		if nb_dim == 1:
			couleur = color(regions[0][1])
			to_plot = regions[0][0].projection().render_line_1d()
			for i in range(1,len(regions)):
				couleur = color(regions[i][1])
				to_plot += regions[i][0].projection().render_line_1d()

		if nb_dim == 2:
			couleur = color(regions[0][1])
			to_plot = regions[0][0].projection().render_fill_2d(color = couleur)
			for i in range(1,len(regions)):
				couleur = color(regions[i][1])
				to_plot += regions[i][0].projection().render_fill_2d(color = couleur)

		if nb_dim == 3:
			couleur = color(regions[0][1])
			to_plot = regions[0][0].projection().render_solid_3d(color = couleur, alpha = 0.7)
			for i in range(1,len(regions)):
				couleur = color(regions[i][1])
				to_plot += regions[i][0].projection().render_solid_3d(color = couleur, alpha = 0.7)
		return to_plot
"

let str_def_regions = 
"#arbre = liste de [region, solution]
def regions_from_tree(arbre, ring, variables, nb_dim):
	regions = []
	lines = []
	if len(variables) == nb_dim:
		for i in range(0,len(arbre)):
			ineqs = [to_ieq(c,ring,variables) for c in arbre[i][0]]
			bind_color(arbre[i][1])
			regions = regions + [[Polyhedron(ieqs = ineqs), arbre[i][1]]]
			lines = lines + [arbre[i][1]]
	if len(variables) + 1 == nb_dim :
		for i in range(0,len(arbre)):
			ineqs = [to_ieq(c,ring,variables)+[0] for c in arbre[i][0]]
			eqs = [to_ieq(-1*arbre[i][1],ring,variables) + [-1]]
			bind_color(arbre[i][1])
			regions = regions + [[Polyhedron(ieqs = ineqs, eqns = eqs), arbre[i][1]]]
			lines = lines + [arbre[i][1]]
	def_colors()
	return (regions,lines)
"

let str_poly_from_regions = 
"def poly_from_regions(regions):
	return [x[0] for x in regions]
"

let str_print_lines = 
"def print_lines(lines, ranges, variables):
	if len(variables) == 2:
		var(variables[0])
		newring = PolynomialRing(QQ,[variables[0]],1)
		p = ring(lines[0])
		c = p.monomial_coefficient(ring(variables[1]))
		g = newring(str((p - c * ring(variables[1])) / (-1*c)))
		couleur = color(p)
		to_plot = plot(g,ranges[0][0],ranges[0][1], color=couleur)
		for i in range(1,len(lines)):
			p = ring(lines[i])
			c = p.monomial_coefficient(ring(variables[1]))
			g = newring(str((p - c * ring(variables[1])) / (-1*c)))
			couleur = color(p)
			to_plot += plot(g,ranges[0][0],ranges[0][1], color=couleur)
		to_plot.show()
"

let str_compute_solution = 
"def compute_output_polyhedron(result, nb_dim, variables):
	solutions = [-1*x[1] for x in result]
	if len(variables) == nb_dim:
		P = Polyhedron(ieqs = [to_ieq(c,ring,parameters) for c in solutions])
	if len(variables) + 1 == nb_dim:	
		ineqs = [to_ieq(c,ring,variables)+[0] for c in solutions]
		eqs = [[0,0,0,1]]
		P = Polyhedron(ieqs = ineqs, eqns = eqs)
		
	if nb_dim == 2:
		return P.projection().render_outline_2d(color = 'black')
	if nb_dim == 3:
		return P.projection().render_wireframe_3d(color = 'black', thickness = 2)
"

let str_plot = 
"to_plot.show()
"
module Cs = PLPCore.Cs
module Cons = PLPCore.Cons

module Plot (Minimization : Min.Type) = struct
	include PLPCore.PLP(Minimization)
	
	module Plot = struct
		module Poly = ParamCoeff.Poly
	
		let (monomial_to_string : Poly.Monomial.t -> string)
			= fun m -> let (vlist, c) = Poly.Monomial.data m in 
			match Poly.MonomialBasis.data vlist with
			| [] -> Q.to_string c
			| _ -> if Q.equal c (Q.of_int 1)
			then Poly.MonomialBasis.to_string_param vlist "p"
			else if Q.lt c (Q.of_int 0) 
				then String.concat "" ["(";Q.to_string c;")*"; Poly.MonomialBasis.to_string_param vlist "p"]
				else String.concat "" [Q.to_string c;"*"; Poly.MonomialBasis.to_string_param vlist "p"]
	
		let polynomial_to_string : Poly.t -> string
			= fun p ->
			Poly.data p
			|> List.map monomial_to_string
			|> String.concat " + "
			|> fun s -> if String.length s = 0 then "0" else s
	
		let (result_to_string : (Region.t * 'c Cons.t) list -> string)
		= fun solutions ->
		Misc.list_to_string 
			(fun (reg,(c,_)) -> Printf.sprintf "[%s,%s]"
				(Misc.list_to_string
					(fun cstr -> 
						let poly = Poly.ofCstr cstr.Cs.v (Scalar.Rat.neg cstr.Cs.c) in
						Printf.sprintf "ring(\"%s\")" (Poly.neg poly |> polynomial_to_string))
					(Region.get_cstrs reg)
					" , ")
				(let cstr = c in
				 let poly = Poly.ofCstr cstr.Cs.v (Scalar.Rat.neg cstr.Cs.c) in
				 Printf.sprintf "ring(\"%s\")" (polynomial_to_string poly))
			)
			solutions ","
	
		let (plot': string -> Poly.V.t list -> int -> (Region.t * 'c Cons.t) list -> unit) 
			= fun file_name parameters nb_dim result ->
			let output_file = open_out file_name in 
			let result_str = result_to_string result in
			let str = Printf.sprintf "%s\n\nparameters = %s\nring = %s\nnb_dim = %s\nresult = %s\n(P,lines) = %s\n%s\n%s"
				(Printf.sprintf "%s%s%s%s%s"
					str_to_ieq
					str_color
					str_def_regions
					str_plot_regions
					str_compute_solution)
				(Misc.list_to_string (fun x -> String.concat "" ["\"";Poly.V.to_string' "p" x;"\""]) parameters ",")
				("PolynomialRing(QQ,parameters,len(parameters))")
				(string_of_int(nb_dim))
				result_str
				(String.concat "\n" ["regions_from_tree(result, ring, parameters, nb_dim)";
				"to_plot = plot_regions(P, nb_dim)"])
				"to_plot += compute_output_polyhedron(result, nb_dim, parameters)"
				(str_plot)
				in print_channel (output_file, str);
				close_out output_file;;
			
		let plot : (Region.t * 'c Cons.t) list -> unit
			= fun res ->
			let parameters = List.split res 
				|> Stdlib.snd
				|> List.split
				|> Stdlib.fst
				|> Cs.getVars
				|> Cs.Vec.V.Set.elements 
			in
			let n_params = List.length parameters in
			let dim = if n_params = 2 then 3 else n_params in
			plot' Config.sage_log parameters dim res
	end
end
		
