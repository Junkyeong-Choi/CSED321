open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = Tml.var -> Tml.tp

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = (fun x -> raise TypeError )

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing cxt e = match e with
	  Tml.Var v -> cxt v
	| Tml.Lam (v, t, e) -> Tml.Fun (t, typing (fun x -> if(x=v) then t else (cxt x)) e)
	| Tml.App (e1, e2) -> (match (typing cxt e1) with
		Tml.Fun (tp1, tp2) -> if (typing cxt e2) = tp1 then tp2 else raise TypeError
		|_ -> raise TypeError)
	| Tml.Pair (e1, e2)-> Tml.Prod ((typing cxt e1),(typing cxt e1))
	| Tml.Fst e -> (match (typing cxt e) with
		Tml.Prod (tp1, tp2) -> tp1
		|_-> raise TypeError)
	| Tml.Snd e -> (match (typing cxt e) with
		Tml.Prod (tp1, tp2) -> tp2
		|_-> raise TypeError)
	| Tml.Eunit -> Tml.Unit
	| Tml.Inl (e, t) -> Tml.Sum(typing cxt e, t)
	| Tml.Inr (e, t) -> Tml.Sum(t, typing cxt e)
	| Tml.Case (e, inlv, inle, inrv, inre) -> (match (typing cxt e) with
		| Tml.Sum(tp1, tp2) -> (if ((typing (fun x -> if(x=inlv) then tp1 else cxt x) inle)=(typing (fun x -> if(x=inrv) then tp2 else cxt x) inre)) then (typing (fun x -> if(x=inrv) then tp2 else cxt x) inre) else raise TypeError)
		| _ -> raise TypeError)
	| Tml.Fix (v,t,e) -> typing (fun x -> if(x=v) then t else (cxt x)) e
	| Tml.True -> Tml.Bool
  	| Tml.False -> Tml.Bool
  	| Tml.Ifthenelse(eIf,eThen,eElse) -> if ((typing cxt eIf) = Tml.Bool) then (if ((typing cxt eThen)=(typing cxt eElse)) then (typing cxt eElse) else raise TypeError) else raise TypeError
  	| Tml.Num i -> Tml.Int
  	| Tml.Plus -> Tml.Fun (Tml.Prod(Tml.Int,Tml.Int),Tml.Int)
  	| Tml.Minus -> Tml.Fun (Tml.Prod(Tml.Int,Tml.Int),Tml.Int)
  	| Tml.Eq -> Tml.Fun (Tml.Prod(Tml.Int,Tml.Int),Tml.Bool)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None
