exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lconcat (l:'a list list) = match l with
[] -> []
|(h::t) -> h @ lconcat t

let rec lfoldl (f:'a * 'b -> 'b) e l = 
		let rec lrev m = match m with
		[] -> []
		|h::t -> lrev t @ [h]
		and rec rfoldl (g:'a *b -> 'b) d n = match n with
		[x] -> g (x,d)
		|h::t -> g (h,rfoldl g d t)
	in rfoldl f e (lrev l)
			 
(** Tail recursive functions  **)

let fact n = 
		let rec fact_aux n acc =
		if (n =0) then acc
		else fact_aux (n-1) (acc*n)
	in fact_aux n 1

let power x n = 
		let rec power_aux x n acc = 
		if (n=0) then acc
		else power_aux (n-1) (acc * x)
	in power_aux x n 1

let fib n = 
		let rec fib_aux n acc1 acc2 =
		if (n=0) then acc1
		else fib_aux (n-1) acc1+acc2 acc1
	in fib_aux n 1 0

let lfilter (p:'a -> bool) l = 
		let rec lfilter_aux (p:'a -> bool) l acc = match l with
		[] -> acc
		|(h::t) -> if (p h) 
	then lfilter_aux t h::acc 
	else lfilter_aux t acc
		in lfilter_aux l []

let ltabulate n (f:int -> 'a) = 
		let rec ltabulate_aux n f acc = 
		if (n=0) then acc
		else ltabulate_aux (n-1) f (acc @ [f n])
	in ltabulate_aux n f []

let rec union l m = 
				let rec isduplicate l x = match l with
				[] -> false
				|(h::t) -> if (h=x) then true else isduplicate t x
		in	match l with
		[] -> m
		|(h::t) -> if(isduplicate m h) then union t m else union t h::m

let inorder t = 
		let inorder_aux t l = match t with
		Leaf x -> x::l
		|Node (t1, x, t2) -> 
	   
let postorder _ = raise NotImplemented

let preorder _ = raise NotImplemented    
		       
(** Sorting in the ascending order **)

let rec quicksort _ = raise NotImplemented

let rec mergesort _ = raise NotImplemented
			
(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = unit       (* dummy type, to be chosen by students *) 
    type 'a heap = unit   (* dummy type, to be chosen by students *)

    let empty _ = raise NotImplemented
    let allocate _ _ = raise NotImplemented
    let dereference _ _ = raise NotImplemented
    let update _ _ _ = raise NotImplemented
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented 
    let insert _ _ = raise NotImplemented
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented
    let insert _ _ = raise NotImplemented
  end
