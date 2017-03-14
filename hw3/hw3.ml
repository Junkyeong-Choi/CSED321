open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = x || y
  let ( ** ) x y = x && y
  let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t and type t = int -> Scal.t
=
struct
  type elem = Scal.t
  type t = int -> elem

  exception VectorIllegal


  let create l = if (l = []) then raise VectorIllegal
  else
    let rec create_aux l length n fnc = match l with
      [] -> fnc
      |(h::t) -> create_aux t length (n-1) (fun x -> if(x = length - n) then h else fnc x)
    and f:int->elem = fun x -> raise VectorIllegal
    in create_aux l (List.length l) (List.length l) f
  
  let dim (f:t) = 
    let rec dim_aux f i value=
      try dim_aux f (i+1) (f i) with _ -> i
    in dim_aux f 0 Scal.zero

  let to_list f = 
    let rec to_list_aux f i l =
      if (i = (dim f)) then l
      else to_list_aux f (i+1) (l@[f i])
    in to_list_aux f 0 []

  let nth f n = f n

  let (++) (f:t) (g:t) = if (dim f <> dim g) then raise VectorIllegal 
                  else create (to_list (fun (i:int) -> Scal.(++) (f i) (g i)))

  let (==) f g = if (dim f <> dim g) then raise VectorIllegal
  else
    let rec equation f g b i =
      if (i = dim f) then b
      else equation f g (b && (Scal.(==) (g i) (f i))) (i+1)
    in equation f g true 0

  let innerp f g = if (dim f <> dim g) then raise VectorIllegal
  else
    let rec innerp_aux f g (value:elem) i =
      if (i = dim f) then value
      else innerp_aux f g (Scal.(++) value (Scal.( ** ) (f i) (g i))) (i+1)
    in innerp_aux f g Scal.zero 0
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = int -> int -> elem

  module ScalVector = VectorFn (Scal)

  exception MatrixIllegal

  let create l = if (l = []) then raise MatrixIllegal
  else if (List.for_all (fun x -> (List.length x = List.length (List.nth l 0)) && (List.length (List.nth l 0) > 0)) l = false) then raise MatrixIllegal
  else 
    let rec create_aux l length n fnc = match l with
      [] -> fnc
      |(h::t) -> create_aux t length (n-1) (fun x -> if(x = length - n) then ScalVector.create h else fnc x)
    and f:t = fun x -> raise MatrixIllegal
    in create_aux l (List.length l) (List.length l) f

  let identity n = if (n<= 0) then raise MatrixIllegal else fun x y ->if((x>=n) || (y>=n)) then raise MatrixIllegal else if(x=y) then Scal.one else Scal.zero
  
  let dim (f:t) = 
    let rec dim_aux f i value=
      (try dim_aux f (i+1) (f i 0) with _ -> i)
     in dim_aux f 0 Scal.zero

  let to_list f = 
    let rec to_list_aux f i l =
      if (i = (dim f)) then l
      else to_list_aux f (i+1) (l @ [ScalVector.to_list (f i)])
    in to_list_aux f 0 []
  
  let transpose f = create (to_list(fun x y -> f y x))
  

  let get f r c = f r c

  let (++) (f:t) (g:t) = if (dim f <> dim g || dim (transpose f) <> dim (transpose g)) then raise MatrixIllegal
  else create (to_list (fun (i:int) (j:int) ->  (Scal.(++) (f i j) (g i j))))
  
  let ( ** ) f g = if (dim g <> dim (transpose f)) then raise MatrixIllegal
                    else create ( to_list (fun (i:int) (j:int) -> (ScalVector.innerp (f i) ((transpose g) j))))

  let (==) f g = if (dim f <> dim g || dim (transpose f) <> dim (transpose g)) then raise MatrixIllegal
  else
    let rec equation f g b i =
      if (i = dim f) then b
      else equation f g (b && (ScalVector.(==) (g i) (f i))) (i+1)
    in equation f g true 0
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure mat_a = 
    let rec closure_aux (current_closure:Mat.t) (given:Mat.t) =
      let dimension_a = Mat.dim current_closure in
    if(Mat.(==) current_closure (Mat.(++) (Mat.identity dimension_a) (Mat.( ** ) (current_closure) (given)))) then current_closure
    else closure_aux  (Mat.(++) (Mat.identity dimension_a) (Mat.( ** ) (current_closure) (given))) given
  in closure_aux (Mat.identity (Mat.dim mat_a)) mat_a
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach (l:bool list list) = BoolMat.to_list(BoolMatClosure.closure(BoolMat.create l))

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = -1
  let one = 0

  let (++) x y = if(x=zero) then y else if (y=zero) then x else if(x>y) then y else x
  let ( ** ) x y = if((x = zero) || (y = zero)) then zero else x + y
  let (==) x y = (x = y)
end

module DistanceMat = MatrixFn (Distance)
module DistanceMatClosure = ClosureFn (DistanceMat)

let distance (l:int list list) = DistanceMat.to_list(DistanceMatClosure.closure(DistanceMat.create l))

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0              (* Plus:Max Mult:min*)
  let one = -1              (* Dummy value : Rewrite it! *)
 
  let (++) x y = if((x = one) || (y = one)) then one else if(x>y) then x else y
  let ( ** ) x y = if (x = one) then y else if(y = one) then x else if (x>y) then y else x
  let (==) x y = (x = y)
end

module WeightMat = MatrixFn (Weight)
module WeightMatClosure = ClosureFn (WeightMat)

let weight (l:int list list) = WeightMat.to_list(WeightMatClosure.closure(WeightMat.create l))

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let testprog =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 
