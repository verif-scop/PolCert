open CWrappers

(* lifting de PedraQ.FullDom *)
module PedraQWrapper: QInterface.HighLevelDomain = struct

    let not_yet_implemented s =
      raise (CertcheckerConfig.CertCheckerFailure (Debugging.NYI, "certified " ^ s ^ " on Q"))

    open DomainInterfaces
    open PedraQ
    include FullDom

    module Term = QInterface.Term

    let is_bottom = isBottom

    let assume c p =
      assume (import_QCond c) p

    let asserts c p =
      coq_assert (import_QCond c) p

    let rename x y = rename (import_certvar x) (import_certvar y)

    let meet p1 p2 =
      not_yet_implemented "meet"

    let assign l p =
      match l with
      | [] -> p
      | [(x, t)] -> FullDom.assign (import_certvar x) (import_QTerm t) p
      | _ -> not_yet_implemented "assign"

    let guassign l c p =
      match l with
      | [] -> p
      | [x] -> FullDom.guassign (import_certvar x) (import_QCond c) p
      | _ -> not_yet_implemented "guassign"


    let rec project l p =
      match l with
      | [] -> p
      | x::l -> project l (FullDom.project p (import_certvar x))

    let leq = isIncl

    (* REALLY INEFFICIENT. TO CHANGE ? *)
    let to_string f p =
      CoqPr.charListTr (to_string (fun x -> CoqPr.stringTr (f (export_certvar x))) p)

    let itvize p t =
      let itv = getItvMode BOTH (import_QTerm t) p in
      { Pol.low = export_QbndT itv.QItv.lower ; Pol.up = export_QbndT itv.QItv.upper }

    (* TODO: getItvMode va t'il renvoyer un intervalle vide? Faut-il lever une exception dans getItvMode plutôt?*)
    let getUpperBound p t =
    	let itv = getItvMode UP (import_QTerm t) p in
    	if QItv.is_bot itv
    	then None
    	else Some (export_QbndT itv.QItv.upper)

    let getLowerBound p t =
    	let itv = getItvMode LOW (import_QTerm t) p in
    	if QItv.is_bot itv
    	then None
    	else Some (export_QbndT itv.QItv.lower)

  	let translate _ _ = not_yet_implemented "translate"

  	let mapi _ _ _ _ = not_yet_implemented "mapi"

  	let minkowski _ _ = not_yet_implemented "minkowski"

	let projectM _ _ = not_yet_implemented "projectM"
end

(* lifting de PedraZ.FullDom *)
module PedraZWrapper: ZInterface.HighLevelDomain = struct

    let not_yet_implemented s =
      raise (CertcheckerConfig.CertCheckerFailure (Debugging.NYI, "certified " ^ s ^ " on Z"))

    open DomainInterfaces
    open PedraZ
    include FullDom

    module Term = ZInterface.Term

    let is_bottom = FullDom.isBottom

    let assume c p =
      assume (import_ZCond c) p

    let asserts c p =
      coq_assert (import_ZCond c) p

    let rename x y = rename (import_certvar x) (import_certvar y)

    let meet p1 p2 =
      not_yet_implemented "meet"

    let join = FullDom.join

    let assign l p =
      match l with
      | [] -> p
      | [(x, t)] -> FullDom.assign (import_certvar x) (import_ZTerm t) p
      | _ -> not_yet_implemented "assign"

    let guassign l c p =
      match l with
      | [] -> p
      | [x] -> FullDom.guassign (import_certvar x) (import_ZCond c) p
      | _ -> not_yet_implemented "guassign"


    let rec project l p =
      match l with
      | [] -> p
      | x::l -> project l (FullDom.project p (import_certvar x))

    let leq = FullDom.isIncl

    (* REALLY INEFFICIENT. TO CHANGE ? *)
    let to_string f p =
      CoqPr.charListTr (FullDom.to_string (fun x -> CoqPr.stringTr (f (export_certvar x))) p)

    let itvize p t =
      let itv = getItvMode BOTH (import_ZTerm t) p in
      { Pol.low = export_ZbndT itv.ZItv.low ; Pol.up = export_ZbndT itv.ZItv.up }

	 (* TODO: getItvMode va t'il lever l'exception?*)
    let getUpperBound p t =
    	try Some (export_ZbndT (getItvMode UP (import_ZTerm t) p).ZItv.up)
    	with Failure s when String.compare s "empty" = 0 -> None

    let getLowerBound p t =
    	try Some (export_ZbndT (getItvMode LOW (import_ZTerm t) p).ZItv.low)
    	with Failure s when String.compare s "empty" = 0 -> None

    let translate _ _ = not_yet_implemented "translate"

    let mapi _ _ _ _ = not_yet_implemented "mapi"

    let minkowski _ _ = not_yet_implemented "minkowski"

	let projectM _ _ = not_yet_implemented "projectM"
end
