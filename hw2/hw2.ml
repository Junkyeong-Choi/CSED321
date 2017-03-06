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
		|Node (t1, x, t2) -> inorder_aux t1 (x::inorder_aux t2 l)
	in inorder_aux t []

let postorder t = 
		let postorder_aux t l = match t with
		Leaf x -> x::l
		|Node (t1, x, t2) -> postorder_aux t1 ((postorder_aux t2 l) @ [x])
	in postorder_aux t []

let preorder t = 
		let preorder_aux t l = match t with
		Leaf x -> l @ [x]
		|Node (t1, x, t2) -> preorder_aux t2 (x::preorder_aux t1 l)
	in preorder_aux t []
		       
(** Sorting in the ascending order **)

let quicksort l = 
		let rec quicksort_aux l m = match l with
		[] -> m
		|[x] -> x::m
		|(h::t) -> 
				let rec divide l x (a,b) = match l with
				[] -> (a,b)
				|(h::t) -> if (h<x) then devide t x (h::a, b)
							else if (h=x) then devide t x (a @ [h], b)
														else devide t x (a, h::b)
		in quicksort_aux (fst (divide t h ([],[]))) (quicksort_aux (snd (divide t h ([],[]))) m)
	in quicksort_aux l []

let mergesort l = 
		let rec mergesort_aux l m = match l with
		[] -> m
		|[x] -> 
				let insert x l =
						let rec insert_aux x l m inserted= match l with
								[] -> if(not inserted) then m@[x]
																		   else m
								|(h::t) -> 
								if(inserted || x>h) then insert_aux x t m@[h] inserted
																		else insert_aux x t m@[x;h] true
				in insert_aux x l [] false
		in	insert x m
		|(h::t) -> 
				let halfsplit l =
						let rec split l (a,b) n = match l with
								[] -> (a,b)
								|(h::t) -> if(n > 0) then split t (h::a, b) (n-1)
																		 else split t (a, h::b) (n-1)
						and length l =
								let rec length_aux l n = match l with
								[] -> n
								|(h::t) -> length_aux t (n+1)
						in length_aux l 0
				in split l ([],[]) (length l)/2
		mergesort_aux (fst(halfsplit l)) (mergesort_aux (snd (halfsplit l)) m)
in mergesort_aux l []
			
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
		
    type loc = int       (* dummy type, to be chosen by students *) 
    type 'a heap = 'a list   (* dummy type, to be chosen by students *)

    let empty () = []
    let allocate h v = (h @ [v], List.length h)
    let dereference h l = try List.nth h l with Failure _ -> raise InvaildLocation
    let update h l v = List.mapi (fun i x -> if (i=l) then v else x) h
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty () = []
    let lookup d k = raise NotImplemented
    let delete d k = raise NotImplemented 
    let insert d (k,v) = raise NotImplemented
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty () = raise NotImplemented
    let lookup d k = raise NotImplemented
    let delete d k = raise NotImplemented
    let insert d k = raise NotImplemented
  end
