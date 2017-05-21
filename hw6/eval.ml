open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible
exception Impossible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = int -> Heap.loc
 and value = 
 LamClosure of env * exp
 |PairClosure of env * exp * exp
 |InlClosure of env * exp
 |InrClosure of env * exp
 |FixClosure of env * exp
 |Vunit 
 |Vtrue 
 |Vfalse 
 |Vnum of int
 |Vplus 
 |Vminus 
 |Veq 

 and frame = 
 Fapp of env * exp
 |Ffst
 |Fsnd
 |Fcase of env * exp * exp
 |Fif of env * exp * exp
 |Fplus
 |Fplusfst of env * exp
 |Fplussnd of value
 |Fminus
 |Fminusfst of env * exp
 |Fminussnd of value
 |Feq
 |Feqfst of env * exp
 |Feqsnd of value
 |Fevaluating of Heap.loc


(* Define your own empty environment *)
let emptyEnv = (fun x -> raise NotConvertible)

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v = match v with
LamClosure (environment , e) -> Lam e
|PairClosure (environment , e1, e2) -> Pair (e1, e2)
|InlClosure (environment , e) -> Inl e
|InrClosure (environment , e) -> Inr e
|FixClosure (environment , e) -> Fix e
|Vunit -> Eunit
|Vtrue -> True
|Vfalse -> False
|Vnum i -> Num i
|Vplus -> Plus
|Vminus -> Minus
|Veq -> Eq


(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp te = let rec
  texp2exp_aux te fixctxt freectxt = match te with
    Tvar (v) -> (try Ind (List.length fixctxt - snd (List.find (fun x -> fst x = v) fixctxt) - 1) 
      with Not_found -> (try Ind (List.length fixctxt + snd (List.find (fun x -> fst x =v) !freectxt)) 
        with Not_found -> (freectxt := !freectxt@[(v, List.length !freectxt)] ; Ind (List.length fixctxt + snd (List.find (fun x -> fst x =v) !freectxt)))
          )
        )
    |Tlam (v,t,te1) -> Lam (texp2exp_aux te1 (fixctxt@[(v, List.length fixctxt)]) freectxt)
    |Tapp (te1,te2) -> let pre = texp2exp_aux te2 fixctxt freectxt in App (texp2exp_aux te1 fixctxt freectxt, pre)
    |Tpair (te1,te2) -> let pre = texp2exp_aux te2 fixctxt freectxt in Pair (texp2exp_aux te1 fixctxt freectxt, pre)
    |Tfst (te1) -> Fst (texp2exp_aux te1 fixctxt freectxt)
    |Tsnd (te1) -> Snd (texp2exp_aux te1 fixctxt freectxt)
    |Teunit -> Eunit
    |Tinl (te1,t) -> Inl (texp2exp_aux te1 fixctxt freectxt)
    |Tinr (te1,t) -> Inr (texp2exp_aux te1 fixctxt freectxt)
    |Tcase (te1,v1,te2,v2,te3) -> 
    let rec convertVar texpr src dst = begin match texpr with
      Tvar (v) -> if (v=dst) then Tvar(src) else Tvar(v)
      |Tlam (v,t,te1) -> if (v=dst) then Tlam(src, t, (convertVar te1 src dst)) else Tlam(v, t, (convertVar te1 src dst))
      |Tapp (te1,te2) -> Tapp (convertVar te1 src dst, convertVar te2 src dst)
      |Tpair (te1,te2) -> Tpair (convertVar te1 src dst, convertVar te2 src dst)
      |Tfst (te1) -> Tfst (convertVar te1 src dst)
      |Tsnd (te1) -> Tsnd (convertVar te1 src dst)
      |Teunit -> Teunit
      |Tinl (te1,t) -> Tinl (convertVar te1 src dst, t)
      |Tinr (te1,t) -> Tinr (convertVar te1 src dst, t)
      |Tcase (te1,v1,te2,v2,te3) -> if (v1=dst) 
      then (if (v2=dst) then Tcase(convertVar te1 src dst, src, convertVar te2 src dst, src, convertVar te3 src dst) else Tcase(convertVar te1 src dst, src, convertVar te2 src dst, v2, convertVar te3 src dst)) 
      else (if (v2=dst) then Tcase(convertVar te1 src dst, v1, convertVar te2 src dst, src, convertVar te3 src dst) else Tcase(convertVar te1 src dst, v1, convertVar te2 src dst, v2, convertVar te3 src dst)) 
      |Tfix (v,t,te1) -> if (v=dst) then Tfix(src, t, (convertVar te1 src dst)) else Tfix(v, t, (convertVar te1 src dst))
      |Ttrue -> Ttrue
      |Tfalse -> Tfalse
      |Tifthenelse (te1,te2,te3) -> Tifthenelse (convertVar te1 src dst, convertVar te2 src dst, convertVar te3 src dst)
      |Tnum i -> Tnum i
      |Tplus -> Tplus
      |Tminus -> Tminus
      |Teq -> Teq
    end
  and prevfreectxt = ref !freectxt
  in
     let pre3 = texp2exp_aux (convertVar te3 v1 v2) (fixctxt@[(v1, List.length fixctxt)]) freectxt 
    and pre2 = texp2exp_aux te2 (fixctxt@[(v1, List.length fixctxt)]) prevfreectxt 
    in Case (texp2exp_aux te1 fixctxt freectxt, pre2, pre3)
    |Tfix (v,t,te1) -> Fix (texp2exp_aux te1 (fixctxt@[(v, List.length fixctxt)]) freectxt)
    |Ttrue -> True
    |Tfalse -> False
    |Tifthenelse (te1,te2,te3) -> let pre3 = texp2exp_aux te3 fixctxt freectxt 
    and pre2 = texp2exp_aux te2 fixctxt freectxt 
    in Ifthenelse (texp2exp_aux te1 fixctxt freectxt, pre2, pre3)
    |Tnum i -> Num i
    |Tplus -> Plus
    |Tminus -> Minus
    |Teq -> Eq
in
  texp2exp_aux te [] (ref [])


(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 exp = 
  let rec sigma n e1 e2 = match e1 with
    Ind x -> let rec tau i n exp = match exp with
      Ind x -> if(x >= i) then Ind (x+n) else Ind x
    | Lam e -> Lam (tau (i+1) n e)
    | App (e1, e2) -> App (tau i n e1, tau i n e2)
    | Pair (e1, e2) -> Pair (tau i n e1, tau i n e2)
    | Fst e -> Fst (tau i n e)
    | Snd e -> Snd (tau i n e)
    | Eunit -> Eunit
    | Inl e -> Inl (tau i n e)
    | Inr e -> Inr (tau i n e)
    | Case (e, e1, e2) -> Case (tau i n e, tau (i) n e1, tau (i) n e2)
    | Fix e -> Fix (tau (i+1) n e)
    | Ifthenelse (e, e1, e2) -> Ifthenelse (tau i n e, tau i n e1, tau i n e2)
    | True -> True
    | False -> False
    | Num n -> Num n
    | Plus -> Plus
    | Minus -> Minus
    | Eq -> Eq
    in if(x < n) then (Ind x) else if (x > n) then (Ind (x-1)) else (tau 0 n e2)
  | Lam e -> Lam(sigma (n+1) e e2)
  | App (exp1, exp2) -> App (sigma n exp1 e2, sigma n exp2 e2)
  | Pair (exp1, exp2) -> Pair (sigma n exp1 e2, sigma n exp2 e2)
  | Fst e -> Fst (sigma n e e2)
  | Snd e -> Snd (sigma n e e2)
  | Eunit -> Eunit
  | Inl e -> Inl (sigma n e e2)
  | Inr e -> Inr (sigma n e e2)
  | Case (e, exp1, exp2) -> Case(sigma n e e2, sigma (n) exp1 e2, sigma (n) exp2 e2)
  | Fix e -> Fix (sigma (n+1) e e2)
  | Ifthenelse (e, exp1, exp2) -> Ifthenelse (sigma n e e2, sigma n exp1 e2, sigma n exp2 e2)
  | True -> True
  | False -> False
  | Num n -> Num n
  | Plus -> Plus
  | Minus -> Minus
  | Eq -> Eq
  in
  match exp with 
    Ind x -> raise Stuck
  | Lam e -> raise Stuck
  | App (e1, e2) -> begin
    try App (step1 e1, e2) with Stuck -> begin
      try App (e1, step1 e2) with Stuck -> begin
        match e1 with 
        | Plus -> begin
            match e2 with
            | Pair(Num n, Num m) -> Num (n + m)
            | _ -> raise Stuck
          end
        | Minus -> begin
            match e2 with
            | Pair(Num n, Num m) -> Num (n - m)
            | _ -> raise Stuck
          end
        | Eq -> begin
            match e2 with
            | Pair(Num n, Num m) -> if(n=m) then True else False
            | _ -> raise Stuck
          end 
        | Lam e -> sigma 0 e e2
        | _ -> raise Stuck
      end
    end
  end
  | Pair (e1, e2) -> begin
    try Pair (step1 e1, e2) with Stuck -> Pair (e1, step1 e2)
  end
  | Fst e ->begin
    try Fst (step1 e) with Stuck -> begin
      match e with
      | Pair (e1, e2) -> e1
      | _ -> raise Stuck
    end
  end 
  | Snd e -> begin
    try Snd (step1 e) with Stuck -> begin
      match e with
      | Pair (e1, e2) -> e2
      | _ -> raise Stuck
    end
  end
  | Eunit -> raise Stuck
  | Inl e -> Inl (step1 e)
  | Inr e -> Inr (step1 e)
  | Case (e, e1, e2) -> begin
    try Case(step1 e, e1, e2) with Stuck -> begin
      match e with
      | Inl v -> sigma 0 e1 v
      | Inr v -> sigma 0 e2 v
      | _ -> raise Stuck
    end
  end
  | Fix e -> sigma 0 e (Fix e)
  | Ifthenelse (e, e1, e2) -> begin
    try Ifthenelse(step1 e, e1, e2) with Stuck -> begin
      match e with
      | True -> e1
      | False -> e2
      | _ -> raise Stuck
    end
  end
  | True -> raise Stuck
  | False -> raise Stuck
  | Num n -> raise Stuck
  | Plus -> raise Stuck
  | Minus -> raise Stuck
  | Eq -> raise Stuck


(* Problem 3. 
 * step2 : state -> state *)
let step2 st = 
  let insertEnv environment l = 
    let size f = 
      let rec size_aux f n value= 
        try size_aux f (n+1) (f n) with _ -> n
    in size_aux f 0 (snd (Heap.allocate Heap.empty 0))
  in (fun x -> if(x=(size environment)) then l else environment x)
in
match st with
Anal_ST (h, sigma, expr, environment) -> begin
   match expr with
   | Ind n -> begin
     match (Heap.deref h (environment n)) with
     | Computed v -> Return_ST (h, sigma, v)
     | Delayed (e, env) -> Anal_ST (h, Frame_SK(sigma, Fevaluating (environment n)), e, env)
   end
   | Lam e -> Return_ST (h, sigma, LamClosure (environment, e))
   | App (e1, e2) -> Anal_ST (h, Frame_SK(sigma, Fapp (environment, e2)), e1, environment)
   | Pair (e1, e2) -> Return_ST (h, sigma, PairClosure (environment, e1, e2))
   | Fst e -> Anal_ST (h, Frame_SK(sigma, Ffst), e, environment)
   | Snd e -> Anal_ST (h, Frame_SK(sigma, Fsnd), e, environment)
   | Eunit -> Return_ST (h, sigma, Vunit)
   | Inl e -> Return_ST (h, sigma, InlClosure (environment, e))
   | Inr e -> Return_ST (h, sigma, InrClosure (environment, e))
   | Case (e, e1, e2) -> Anal_ST (h, Frame_SK(sigma, Fcase (environment, e1, e2)), e, environment)
   | Fix e -> Return_ST (h, sigma, FixClosure (environment, e))
   | Ifthenelse (e, e1, e2) -> Anal_ST (h, Frame_SK(sigma, Fif(environment, e1, e2)), e, environment)
   | True -> Return_ST (h, sigma, Vtrue)
   | False -> Return_ST (h, sigma, Vfalse)
   | Num n -> Return_ST (h, sigma, Vnum n)
   | Plus -> Return_ST (h, sigma, Vplus)
   | Minus -> Return_ST (h, sigma, Vminus)
   | Eq -> Return_ST (h, sigma, Veq)
 end
| Return_ST (h, sigma, v) -> begin
   match (sigma, v) with
    (Frame_SK(s, Fevaluating l), _) -> let h1 = Heap.update h l (Computed v) in Return_ST(h1, s, v)
  | (Frame_SK(s, Fapp (env0, e2)), LamClosure (env1, e1)) -> 
  let env2 = let l = snd (Heap.allocate h (Delayed (e2, env0))) in insertEnv env1 l
  and h1 = fst (Heap.allocate h (Delayed (e2, env0)))
   in Anal_ST (h1, s, e1, env2)
  | (Frame_SK(s, Fapp (env0, e2)), FixClosure (env1, e1)) -> begin match e1 with
    | Lam e1' -> 
    let env3 = 
      let env2 = 
        let l0 = snd(Heap.allocate h (Delayed (e2, env0)))
      in insertEnv env1 l0
      and l1 = 
        let h1 = fst(Heap.allocate h (Delayed (e2, env0)))
      in snd (Heap.allocate h1 (Computed (FixClosure (env1, e1))))
    in insertEnv env2 l1
    and h2 =
      let h1 = fst(Heap.allocate h (Delayed (e2, env0)))
    in fst (Heap.allocate h1 (Computed (FixClosure (env1, e1))))
  in Anal_ST (h2, s, e1', env3)
    | _ -> raise NotConvertible
  end
  | (Frame_SK(s, Fapp (env0, e2)), Vplus) -> Anal_ST (h, Frame_SK(s, Fplus), e2, env0)
  | (Frame_SK(s, Fapp (env0, e2)), Vminus) -> Anal_ST (h, Frame_SK(s, Fminus), e2, env0)
  | (Frame_SK(s, Fapp (env0, e2)), Veq) -> Anal_ST (h, Frame_SK(s, Feq), e2, env0)
  | (Frame_SK(s, Ffst), PairClosure (env, e1, e2)) -> Anal_ST (h, s, e1, env)
  | (Frame_SK(s, Fsnd), PairClosure (env, e1, e2)) -> Anal_ST (h, s, e2, env)
  | (Frame_SK(s, Fcase (env1, e1, e2)), InlClosure (env0, e)) -> 
  let env2 = let l = snd (Heap.allocate h (Delayed (e, env0))) in insertEnv env1 l
  and h1 = fst (Heap.allocate h (Delayed (e, env0)))
in Anal_ST (h1, s, e1, env2)
  | (Frame_SK(s, Fcase (env1, e1, e2)), InrClosure (env0, e)) -> 
  let env2 = let l = snd (Heap.allocate h (Delayed (e, env0))) in insertEnv env1 l
  and h1 = fst (Heap.allocate h (Delayed (e, env0)))
in Anal_ST (h1, s, e2, env2)
  | (Frame_SK(s, Fif (env, e1, e2)), Vtrue) -> Anal_ST (h, s, e1, env)
  | (Frame_SK(s, Fif (env, e1, e2)), Vfalse) -> Anal_ST (h, s, e2, env)
  | (Frame_SK(s, Fplus), PairClosure (env, e1, e2)) -> Anal_ST (h, Frame_SK(s, Fplusfst (env, e2)), e1, env)
  | (Frame_SK(s, Fplusfst (env, e2)), _) -> Anal_ST (h, Frame_SK(s, Fplussnd v), e2, env)
  | (Frame_SK(s, Fplussnd v1), v2) -> begin
    match (v1, v2) with
    | (Vnum n, Vnum m) -> Return_ST (h, s, Vnum (n+m))
    | _ -> raise NotConvertible
  end
  | (Frame_SK(s, Fminus), PairClosure (env, e1, e2)) -> Anal_ST (h, Frame_SK(s, Fminusfst (env, e2)), e1, env)
  | (Frame_SK(s, Fminusfst (env, e2)), _) -> Anal_ST (h, Frame_SK(s, Fminussnd v), e2, env)
  | (Frame_SK(s, Fminussnd v1), v2) ->  begin
    match (v1, v2) with
    | (Vnum n, Vnum m) -> Return_ST (h, s, Vnum (n-m))
    | _ -> raise NotConvertible
  end
  | (Frame_SK(s, Feq), PairClosure (env, e1, e2)) -> Anal_ST (h, Frame_SK(s, Feqfst (env, e2)), e1, env)
  | (Frame_SK(s, Feqfst (env, e2)), _) -> Anal_ST (h, Frame_SK(s, Feqsnd v), e2, env)
  | (Frame_SK(s, Feqsnd v1), v2) -> begin
    match (v1, v2) with
    | (Vnum n, Vnum m) -> if (n=m) then Return_ST (h, s, Vtrue) else Return_ST (h, s, Vfalse)
    | _ -> raise NotConvertible
  end
  | (Hole_SK, _) -> raise Stuck
  | _ -> raise NotConvertible
end


(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = 
  let heap2string h = raise NotImplemented
  and stack2string s = raise NotImplemented
  and env2string e = raise NotImplemented
  and value2string v = exp2string (value2exp v)
in match st with
    Anal_ST(_,_,exp,_) -> "Analysis" ^ exp2string exp
  | Return_ST(_,_,v) -> "Returning" ^ value2string v

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
