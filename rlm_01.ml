
(* References:
   Andrzej Filinski, Representing Layered Monads, POPL 1999
   Andrzej Filinski, Monadic Reflection in Haskell, 2006 *)

type 'a writer = 'a * string
let id a = a

module type MONAD =
  sig
    type 'a exp
    val ereturn : 'a -> 'a exp
    val elet    : 'a exp -> ('a -> 'b exp) -> 'b exp
  end

module type MONAD_WITH_RUN =
  sig
    include MONAD
    val run : 'a exp -> 'a
  end

module IdMonad =
  struct
    type 'a exp = 'a
    let ereturn a = a
    let elet a f = f a
    let run a = a
  end

module type LAYER =
  sig
    include MONAD
    type 'a prev
    type 'a t
    val lift    : 'a prev -> 'a exp
    val reify   : 'a exp -> 'a t prev
    val reflect : 'a t prev -> 'a exp
  end

module ListA (T : MONAD) =
  struct
    type 'a exp  = 'a list T.exp
    type 'a prev = 'a T.exp
    type 'a t    = 'a list

    let appendT tla1 tla2 =
      T.elet tla1 (fun la1 ->
          T.elet tla2 (fun la2 ->
              T.ereturn (la1 @ la2)))

    let ereturn a =
      T.ereturn [a]

    let elet tla f =
      let rec loop la =
        match la with
        | [] -> T.ereturn []
        | a :: la -> appendT (f a) (loop la) in
      T.elet tla loop

    let reify   = id
    let reflect = id
    let lift ta = T.elet ta ereturn
  end

module WriterA (T : MONAD) =
  struct
    type 'a exp  = 'a writer T.exp
    type 'a prev = 'a T.exp
    type 'a t    = 'a writer

    let ereturn a =
      T.ereturn (a, "")

    let elet twa f =
      T.elet twa (fun (a, s1) ->
          T.elet (f a) (fun (b, s2) ->
              T.ereturn (b, s1 ^ s2)))

    let reify   = id
    let reflect = id
    let lift ta = T.elet ta ereturn
  end

module OptionA (T : MONAD) =
  struct
    type 'a exp  = 'a option T.exp
    type 'a prev = 'a T.exp
    type 'a t    = 'a option

    let ereturn a =
      T.ereturn (Some a)

    let elet toa f =
      T.elet toa (fun oa ->
          match oa with
          | Some a -> f a
          | None   -> T.ereturn None)

    let reify   = id
    let reflect = id
    let lift ta = T.elet ta ereturn
  end

module Cont (T : MONAD) =
  struct
    type 'a exp = { ka : 'r. ('a -> 'r T.exp) -> 'r T.exp }

    let ereturn a =
      { ka = fun k -> k a }

    let elet ka f =
      { ka = fun k -> ka.ka (fun a -> (f a).ka k) }

    let reify ka =
      ka.ka T.ereturn

    let reflect ta =
      { ka = fun k -> T.elet ta k }

    let lift =
      reflect
  end

module ListB (T : MONAD) =
  struct
    module L = ListA(T)
    module C = Cont(L)

    type 'a exp  = 'a C.exp
    type 'a prev = 'a L.prev
    type 'a t    = 'a list

    let ereturn a = C.ereturn a
    let elet ka f = C.elet ka f

    let reify ka  = L.reify (C.reify ka)
    let reflect a = C.reflect (L.reflect a)
    let lift a    = C.lift (L.lift a)
  end

module WriterB (T : MONAD) =
  struct
    module W = WriterA(T)
    module C = Cont(W)

    type 'a exp  = 'a C.exp
    type 'a prev = 'a W.prev
    type 'a t    = 'a writer

    let ereturn a = C.ereturn a
    let elet ka f = C.elet ka f

    let reify ka  = W.reify (C.reify ka)
    let reflect a = C.reflect (W.reflect a)
    let lift a    = C.lift (W.lift a)
  end

module OptionB (T : MONAD) =
  struct
    module O = OptionA(T)
    module C = Cont(O)

    type 'a exp  = 'a C.exp
    type 'a prev = 'a O.prev
    type 'a t    = 'a option

    let ereturn a = C.ereturn a
    let elet ka f = C.elet ka f

    let reify ka  = O.reify (C.reify ka)
    let reflect a = C.reflect (O.reflect a)
    let lift a    = C.lift (O.lift a)
  end

module ListC (T : MONAD) =
  struct
    type 'a exp  = { ka : 'r. ('a -> 'r list T.exp) -> 'r list T.exp }
    type 'a prev = 'a T.exp
    type 'a t    = 'a list

    let appendT tla1 tla2 =
      T.elet tla1 (fun la1 ->
          T.elet tla2 (fun la2 ->
              T.ereturn (la1 @ la2)))

    let reify ka =
      ka.ka (fun a -> T.ereturn [a])

    let reflect tla =
      { ka =
          fun f ->
          let rec loop la =
            match la with
            | [] -> T.ereturn []
            | a :: la -> appendT (f a) (loop la) in
          T.elet tla loop }

    let lift ka =
      { ka = fun f -> T.elet ka f }

    let ereturn a =
      { ka = fun k -> k a }

    let elet ka f =
      { ka = fun k -> ka.ka (fun a -> (f a).ka k) }
end

module WriterC (T : MONAD) =
  struct
    type 'a exp  = { ka : 'r. ('a -> 'r writer T.exp) -> 'r writer T.exp }
    type 'a prev = 'a T.exp
    type 'a t    = 'a writer

    let reify ka =
      ka.ka (fun a -> T.ereturn (a, ""))

    let reflect twa =
      { ka =
          fun f ->
          T.elet twa (fun (a, s1) ->
              T.elet (f a) (fun (b, s2) ->
                  T.ereturn (b, s1 ^ s2))) }

    let lift ka =
      { ka = fun f -> T.elet ka f }

    let ereturn a =
      { ka = fun k -> k a }

    let elet ka f =
      { ka = fun k -> ka.ka (fun a -> (f a).ka k) }
  end

module OptionC (T : MONAD) =
  struct
    type 'a exp  = { ka : 'r. ('a -> 'r option T.exp) -> 'r option T.exp }
    type 'a prev = 'a T.exp
    type 'a t    = 'a option

    let reify ka =
      ka.ka (fun a -> T.ereturn (Some a))

    let reflect toa =
      { ka =
          fun f ->
          T.elet toa (fun oa ->
              match oa with
              | Some a -> f a
              | None   -> T.ereturn None) }

    let lift ka =
      { ka = fun f -> T.elet ka f }

    let ereturn a =
      { ka = fun k -> k a }

    let elet ka f =
      { ka = fun k -> ka.ka (fun a -> (f a).ka k) }
end

module type LAYERS =
  sig
    type 'a exp0
    type 'a exp1
    type 'a exp2
    type 'a exp3

    val run0 : 'a exp0 -> 'a

    val ereturn0 : 'a -> 'a exp0
    val ereturn1 : 'a -> 'a exp1
    val ereturn2 : 'a -> 'a exp2
    val ereturn3 : 'a -> 'a exp3

    val elet0 : 'a exp0 -> ('a -> 'b exp0) -> 'b exp0
    val elet1 : 'a exp1 -> ('a -> 'b exp1) -> 'b exp1
    val elet2 : 'a exp2 -> ('a -> 'b exp2) -> 'b exp2
    val elet3 : 'a exp3 -> ('a -> 'b exp3) -> 'b exp3

    val lift1 : 'a exp0 -> 'a exp1
    val lift2 : 'a exp1 -> 'a exp2
    val lift3 : 'a exp2 -> 'a exp3

    val reify1 : 'a exp1 -> 'a list   exp0
    val reify2 : 'a exp2 -> 'a writer exp1
    val reify3 : 'a exp3 -> 'a option exp2

    val reflect1 : 'a list   exp0 -> 'a exp1
    val reflect2 : 'a writer exp1 -> 'a exp2
    val reflect3 : 'a option exp2 -> 'a exp3
  end

module LayersFrom
         (L0 : MONAD_WITH_RUN)
         (L1 : LAYER with type 'a prev = 'a L0.exp and type 'a t = 'a list)
         (L2 : LAYER with type 'a prev = 'a L1.exp and type 'a t = 'a writer)
         (L3 : LAYER with type 'a prev = 'a L2.exp and type 'a t = 'a option) =
  struct
    type 'a exp0 = 'a L0.exp
    type 'a exp1 = 'a L1.exp
    type 'a exp2 = 'a L2.exp
    type 'a exp3 = 'a L3.exp
    
    let run0 = L0.run

    let ereturn0 = L0.ereturn
    let ereturn1 = L1.ereturn
    let ereturn2 = L2.ereturn
    let ereturn3 = L3.ereturn

    let elet0 = L0.elet
    let elet1 = L1.elet
    let elet2 = L2.elet
    let elet3 = L3.elet

    let lift1 = L1.lift
    let lift2 = L2.lift
    let lift3 = L3.lift

    let reify1 = L1.reify
    let reify2 = L2.reify
    let reify3 = L3.reify

    let reflect1 = L1.reflect
    let reflect2 = L2.reflect
    let reflect3 = L3.reflect
  end

module type LANG =
  sig
    include MONAD
    val eseq   : 'a exp -> 'b exp -> 'b exp
    val pick   : 'a list -> 'a exp
    val write  : string -> unit exp
    val eraise : unit -> 'a exp
    val handle : 'a exp -> 'a exp -> 'a exp
    val run    : 'a exp -> 'a option writer list
  end

module Lang (L : LAYERS) =
  struct
    type 'a exp = 'a L.exp3

    let ereturn a  = L.ereturn3 a
    let elet e f   = L.elet3 e f
    let eseq e1 e2 = L.elet3 e1 (fun _ -> e2)

    let pick l =
      L.lift3 (L.lift2 (L.reflect1 (L.ereturn0 l)))

    let write s =
      L.lift3 (L.reflect2 (L.ereturn1 ((), s)))

    let eraise () =
      L.reflect3 (L.ereturn2 None)

    let handle e1 e2 =
      L.elet3 (L.lift3 (L.reify3 e1)) (fun oa ->
          match oa with
          | Some a -> L.ereturn3 a
          | None   -> e2)

    let run e =
      L.run0 (L.reify1 (L.reify2 (L.reify3 e)))
  end

module Example01 (L : LANG) =
  struct
    let ex_01 =
      L.run
        (L.handle
           (L.elet (L.pick [1; 2; 3; 4; 5]) (fun a ->
                L.eseq (L.write ("a=" ^ (string_of_int a)))
                  (L.eseq (if a * a = 9
                           then L.eseq (L.write "!") (L.eraise ())
                           else L.write "ok")
                     (L.ereturn (10 * a)))))
           (L.eseq (L.write "H")
              (L.elet (L.pick [true; false]) (fun b ->
                   if b
                   then L.eseq (L.write "yes") (L.ereturn 42)
                   else (L.eraise ())))))
  end

module A0 = IdMonad
module A1 = ListA(A0)
module A2 = WriterA(A1)
module A3 = OptionA(A2)
module LayersA = LayersFrom(A0)(A1)(A2)(A3)
module Ex01A = Example01(Lang(LayersA))

module B0 = IdMonad
module B1 = ListB(B0)
module B2 = WriterB(B1)
module B3 = OptionB(B2)
module LayersB = LayersFrom(B0)(B1)(B2)(B3)
module Ex01B = Example01(Lang(LayersB))

module C0 = IdMonad
module C1 = ListC(C0)
module C2 = WriterC(C1)
module C3 = OptionC(C2)
module LayersC = LayersFrom(C0)(C1)(C2)(C3)
module Ex01C = Example01(Lang(LayersC))

let ex_01A = Ex01A.ex_01
let ex_01B = Ex01B.ex_01
let ex_01C = Ex01C.ex_01

;;
