
(* References:
   Andrzej Filinski, Representing Layered Monads, POPL 1999
   Andrzej Filinski, Monadic Reflection in Haskell, 2006 *)

let returnK a k =
  k a

let letK ka f k =
  ka (fun a -> f a k)

let runK ka =
  ka (fun a -> a)

module ListK =
  struct
    let appendK kla1 kla2 =
      letK kla1 (fun la1 ->
          letK kla2 (fun la2 ->
              returnK (la1 @ la2)))

    let reify ka =
      ka (fun a -> returnK [a])

    let reflect tla f =
      let rec loop la =
        match la with
        | [] -> returnK []
        | a :: la -> appendK (f a) (loop la) in
      letK tla loop
  end

module WriterK =
  struct
    let reify ka =
      ka (fun a -> returnK (a, ""))

    let reflect twa f =
      letK twa (fun (a, s1) ->
          letK (f a) (fun (b, s2) ->
              returnK (b, s1 ^ s2)))
  end

module OptionK =
  struct
    let reify ka =
      ka (fun a -> returnK (Some a))

    let reflect toa f =
      letK toa (fun oa ->
          match oa with
          | Some a -> f a
          | None   -> returnK None)
  end

module Layers =
  struct
    let run0 = runK

    let ereturn0 = returnK
    let ereturn1 = returnK
    let ereturn2 = returnK
    let ereturn3 = returnK

    let elet0 = letK
    let elet1 = letK
    let elet2 = letK
    let elet3 = letK
    
    let lift1 = letK
    let lift2 = letK
    let lift3 = letK

    let reify1 = ListK.reify
    let reify2 = WriterK.reify
    let reify3 = OptionK.reify

    let reflect1 = ListK.reflect
    let reflect2 = WriterK.reflect
    let reflect3 = OptionK.reflect
  end

module Lang =
  struct
    module L = Layers

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

module Example01 =
  struct
    module L = Lang

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

let ex_01 = Example01.ex_01

;;
