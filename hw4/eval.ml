(*
 * Call-by-value reduction   
 *)

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))


(*
 * for given expression e, return the list of free variables in type of Uml.var
 *)
let rec freeVar (e:Uml.exp) = match e with
	Uml.Var v -> [v]
	|Uml.Lam (v,exp) -> 
	let exclude l x =
		let rec exclude_rec l x ret = match l with
			[] -> ret
			|(h::t) -> if(x = h) then exclude_rec t x ret else exclude_rec t x ret@[h]
		in exclude_rec l x []
	in exclude (freeVar exp) v
	|Uml.App (exp1,exp2) -> 
	let union l m =
		let rec removeDuplicates l ret = 
			let rec exclude_rec l x ret = match l with
				[]-> ret
				|(h::t) -> if(x=h) then exclude_rec t x ret else exclude_rec t x ret@[h]
			in match l with
			[] -> ret
			|(h::t) -> removeDuplicates (exclude_rec t h []) (ret@[h])
		in removeDuplicates (l@m) []
	in union (freeVar exp1) (freeVar exp2)

(*
 * swap two variables on given expression
 *)
let rec swap var1 var2 e = match e with
	Uml.Var v -> 
	if(v = var1) then (Uml.Var var2) 
	else if(v = var2) then (Uml.Var var1) 
	else (Uml.Var v)
	|Uml.Lam (v, exp) -> 
	if(v = var1) then Uml.Lam (var2, (swap var1 var2 exp)) 
	else if(v = var2) then Uml.Lam (var1, (swap var1 var2 exp)) 
	else Uml.Lam (v, (swap var1 var2 exp))
	|Uml.App(exp1, exp2) -> Uml.App((swap var1 var2 exp1),(swap var1 var2 exp2))


(*
 *  substitute e1 for every occurence of var in e2, that is [e1/var]e2
 *)
let rec substitute e1 var e2 = match e2 with
	Uml.Var v -> 
	if(v = var) then e1
	else e2
	|Uml.Lam (v, exp) ->
	if(v = var) then e2
	else if(List.for_all (fun x -> (x!=v)) (freeVar e1)) then Uml.Lam(v, (substitute e1 var exp))
	else 
		let freshVar = getFreshVariable v in
		Uml.Lam(freshVar, (substitute e1 var (swap v freshVar exp)))
	|Uml.App(exp1, exp2) -> Uml.App ((substitute e1 var exp1), (substitute e1 var exp2))
               
(*
 * implement a single step with reduction using the call-by-value strategy.
 *)

let rec stepv e = match e with
	Uml.App (exp1, exp2) -> (match exp1 with
		Uml.Lam (v, exp) -> (match exp2 with
			Uml.Lam (var, exp3) ->substitute exp2 v exp
			|_ -> Uml.App(exp1, (stepv exp2)))
		| _ -> Uml.App((stepv exp1),exp2))
	|_ -> raise Stuck

(*
let rec stepv e = match e with
	Uml.App (exp1, exp2) -> 
		(try Uml.App((stepv exp1), exp2) with Stuck ->(match exp1 with
			Uml.Lam(v, exp) -> (match exp2 with
				Uml.Lam (dummy1, dummy2) -> substitute exp2 v exp
				|_ -> Uml.App(exp1, (stepv exp2)))
			|_-> raise Stuck))
	|_ -> raise Stuck
*)


(*
 * implement a single step with reduction using the call-by-name strategy.
 *)


let rec stepn e = match e with
	Uml.App (exp1, exp2) -> (match exp1 with
		Uml.Lam (v, exp) ->substitute exp2 v exp
		| _ -> Uml.App((stepn exp1),exp2))
	|_ -> raise Stuck

(*
let rec stepn e = match e with
	Uml.App (exp1, exp2) -> 
		(try Uml.App((stepn exp1),exp2) with Stuck ->(match exp1 with
			Uml.Lam(v,exp) -> substitute exp2 v exp
			|_ -> raise Stuck))
	|_ -> raise Stuck


*)
let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

