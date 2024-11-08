
(* Monad Translations Compose *)

module type LANG =
  sig
    type exp

    val unit : exp
    val int : int -> exp
    val string : string -> exp

    val pair : exp -> exp -> exp
    val left : exp -> exp
    val right : exp -> exp

    val inleft : exp -> exp
    val inright : exp -> exp
    val case : exp -> (exp -> exp) -> (exp -> exp) -> exp

    val elet : exp -> (exp -> exp) -> exp
    val lam : (exp -> exp) -> exp
    val rlam : (exp -> exp -> exp) -> exp

    val app : exp -> exp -> exp

    val nil : exp
    val cons : exp -> exp -> exp
    val fold : exp -> exp -> exp -> exp

    type result
    val show : exp -> result

    val ops : (string * (bool * exp)) list
  end

module Ext(L : LANG) =
  struct
    let etrue = L.inleft L.unit
    let efalse = L.inright L.unit

    let list es = List.fold_right L.cons es L.nil

    let app2 e1 e2 e3 = L.app (L.app e1 e2) e3
    let appp e1 e2 e3 = L.app e1 (L.pair e2 e3)

    let seq e1 e2 =
      L.elet e1 (fun _ -> e2)

    let compose e1 e2 =
      L.lam (fun x -> L.app e1 (L.app e2 x))

    let op name =
      match List.assoc_opt name L.ops with
      | Some (ty, op) -> op
      | None -> raise (Failure ("op not found: " ^ name))

    let reflect =
      L.lam (fun l -> l)

    let reify mreturn =
      L.lam (fun t ->
          L.app (L.lam mreturn) (L.app t L.unit))
  end

module Lang =
  struct
    type exp =
      | Unit
      | Int of int
      | String of string
      | Pair of exp * exp
      | InLeft of exp
      | InRight of exp
      | Lam of (exp -> exp)
      | RLam of (exp -> exp -> exp)
      | List of exp list

    let unit = Unit
    let int k = Int k
    let string s = String s

    let pair e1 e2 = Pair (e1, e2)

    let left e =
      match e with
      | Pair (e1, e2) -> e1
      | _ -> raise (Failure "left expected pair")

    let right e =
      match e with
      | Pair (e1, e2) -> e2
      | _ -> raise (Failure "right expected pair")

    let inleft e = InLeft e
    let inright e = InRight e

    let case e f1 f2 =
      match e with
      | InLeft e1 -> f1 e1
      | InRight e2 -> f2 e2
      | _ -> raise (Failure "case expected inject")

    let elet e f = f e
    let lam f = Lam f
    let rlam f = RLam f

    let app e1 e2 =
      match e1 with
      | Lam f -> f e2
      | RLam f -> f e1 e2
      | _ -> raise (Failure "app expected lam")

    let nil = List []

    let cons e l =
      match l with
      | List l -> List (e :: l)
      | _ -> raise (Failure "cons expected list")

    let fold nil cons l =
      let cons2 x y =
        app (app cons x) y in
      match l with
      | List l -> List.fold_right cons2 l nil
      | _ -> raise (Failure "fold expected list")

    type result = exp
    let show e = e

    let int_to_string_op =
      lam (fun v ->
          match v with
          | Int n -> String (string_of_int n)
          | _ -> raise (Failure "int_to_string expected int")
        )

    let plus_op =
      lam (fun xy ->
          match (left xy, right xy) with
          | (Int a, Int b) -> Int (a + b)
          | _ -> raise (Failure "plus expected int")
        )

    let times_op =
      lam (fun xy ->
          match (left xy, right xy) with
          | (Int a, Int b) -> Int (a * b)
          | _ -> raise (Failure "times expected int")
        )

    let concat_op =
      lam (fun xy ->
          match (left xy, right xy) with
          | (String a, String b) -> String (a ^ b)
          | _ -> raise (Failure "concat expected string")
        )

    let append_op =
      lam (fun xy ->
          match (left xy, right xy) with
          | (List a, List b) -> List (a @ b)
          | _ -> raise (Failure "append expected list")
        )

    let equals_op =
      lam (fun xy ->
          if (left xy) = (right xy)
          then inleft unit
          else inright unit
        )

    let ops = [
        ("int_to_string", (true, int_to_string_op));
        ("plus", (true, plus_op));
        ("times", (true, times_op));
        ("concat", (true, concat_op));
        ("append", (true, append_op));
        ("equals", (true, equals_op));
      ]
  end

module type MONAD =
  sig
    type exp
    val mreturn : exp -> exp
    val mlet : exp -> (exp -> exp) -> exp
    val mshow : exp -> exp
    val ops : (string * (bool * exp)) list
  end

module IdentityMonad(L : LANG) =
  struct

    (* identity a = a *)

    type exp = L.exp

    let mreturn a = a

    let mlet ma f =
      L.app (L.lam f) ma

    let mshow e = e

    let ops = []
  end

module ListMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* list a = list a *)

    type exp = L.exp

    let mreturn a =
      X.list [a]

    let mlet ma f =
      L.fold L.nil
        (L.lam (fun a ->
             L.lam (fun mb ->
                 X.appp (X.op "append")
                   (L.app (L.lam f) a)
                   mb)))
        ma

    let mshow e = e

    let pick_op =
      L.lam (fun l -> l)

    let amb_op =
      L.lam (fun t1_t2 ->
          X.appp (X.op "append")
            (L.app (L.left t1_t2) L.unit)
            (L.app (L.right t1_t2) L.unit))

    let ops = [
        ("reflect_list", (false, mreturn X.reflect));
        ("reify_list", (true, mreturn (X.reify mreturn)));
        ("pick", (true, mreturn pick_op));
        ("amb", (false, mreturn amb_op))
      ]
  end

module ExceptionMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* exception a = a + X *)

    type exp = L.exp

    let mreturn a =
      L.inleft a

    let mlet ma f =
      L.case ma
        (fun a -> L.app (L.lam f) a)
        (fun x -> L.inright x)

    let mshow e = e

    let raise_op =
      L.lam (fun _ -> L.inright L.unit)

    let handle_op =
      L.lam (fun t1_t2 ->
          L.case (L.app (L.left t1_t2) L.unit)
            (fun a -> L.inleft a)
            (fun _ -> L.app (L.right t1_t2) L.unit))

    let ops = [
        ("reflect_exception", (false, mreturn X.reflect));
        ("reify_exception", (true, mreturn (X.reify mreturn)));
        ("raise", (false, mreturn raise_op));
        ("handle", (false, mreturn handle_op))
      ]
  end

module ReaderMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* reader a = X -> a *)

    type exp = L.exp

    let mreturn a =
      L.lam (fun _ -> a)

    let mlet ma f =
      L.lam (fun x ->
          X.app2 (L.lam f) (L.app ma x) x)

    let mshow e =
      L.app e (L.int 0)

    let read_op =
      L.lam (fun _ -> L.lam (fun x -> x))

    let with_op =
      L.lam (fun x_t ->
          L.lam (fun _ ->
              X.app2 (L.right x_t) L.unit (L.left x_t)))

    let ops = [
        ("read", (true, mreturn read_op));
        ("with", (false, mreturn with_op))
      ]
  end

module WriterMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* writer a = a * string *)

    type exp = L.exp

    let mreturn a =
      L.pair a (L.string "")

    let mlet ma f =
      L.elet ma (fun ma ->
          let a = L.left ma in
          let s1 = L.right ma in
          L.elet (L.app (L.lam f) a) (fun mb ->
              let b = L.left mb in
              let s2 = L.right mb in
              L.pair b (X.appp (X.op "concat") s1 s2)))

    let mshow e = e

    let write_op =
      L.lam (fun s -> L.pair L.unit s)

    let ops = [
        ("reflect_writer", (false, mreturn X.reflect));
        ("reify_writer", (true, mreturn (X.reify mreturn)));
        ("write", (true, mreturn write_op))
      ]
  end

module StateMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* state a = S -> a * S *)

    type exp = L.exp

    let mreturn a =
      L.lam (fun s ->
          L.pair a s)

    let mlet ma f =
      L.lam (fun s ->
          L.elet (L.app ma s) (fun a_s ->
              let a = L.left a_s in
              let s = L.right a_s in
              X.app2 (L.lam f) a s))

    let mshow e =
      L.app e (L.int 0)

    let get_op =
      L.lam (fun _ -> L.lam (fun s -> L.pair s s))

    let set_op =
      L.lam (fun v -> L.lam (fun s -> L.pair L.unit v))

    let ops = [
        ("get", (true, mreturn get_op));
        ("set", (true, mreturn set_op))
      ]

    let fetch_op yield get =
      L.lam (fun u ->
          L.app yield get)

    let store_op yield set =
      L.lam (fun e ->
          L.app yield
            (L.lam (fun u -> L.app set e)))
  end

module ContinuationMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* continuation a = forall r. (a -> r) -> r *)

    type exp = L.exp

    let mreturn a =
      L.lam (fun k -> L.app k a)

    let mlet ma f =
      L.lam (fun k ->
          L.app ma (L.lam (fun a -> X.app2 (L.lam f) a k)))

    let mshow e =
      L.app e (L.lam (fun v -> v))

    let ops = []
  end

module ResumptionMonad(L : LANG) =
  struct
    module X = Ext(L)

    (* resumption a = fix r. 1 -> a + r *)

    type exp = L.exp

    let mreturn a =
      L.lam (fun _ -> L.inleft a)

    let mlet ma f =
      L.app
        (L.rlam (fun loop ma ->
             L.lam (fun _ ->
                 L.case (L.app ma L.unit)
                   (fun a -> X.app2 (L.lam f) a L.unit)
                   (fun r -> L.inright (L.app loop r)))))
        ma

    let mshow =
      L.app
        (L.rlam (fun show r ->
             L.case (L.app r L.unit)
               (fun a -> a)
               (fun r -> L.app show r)))

    let yield_op =
      L.lam (fun t ->
          L.lam (fun _ ->
              L.inright (L.app t L.unit)))

    let atomic_op =
      L.lam (fun t ->
          L.lam (fun _ ->
              L.inleft
                (L.app
                   (L.rlam (fun loop r ->
                        L.case (L.app r L.unit)
                          (fun a -> a)
                          (fun r -> L.app loop r)))
                   (L.app t L.unit))))

    let par amb =
      let pair_left =
        L.lam (fun a ->
            L.rlam (fun loop r ->
                L.lam (fun _ ->
                    L.case (L.app r L.unit)
                      (fun b -> L.inleft (L.pair a b))
                      (fun r -> L.inright (L.app loop r))))) in
      let pair_right =
        L.lam (fun b ->
            L.rlam (fun loop r ->
                L.lam (fun _ ->
                    L.case (L.app r L.unit)
                      (fun a -> L.inleft (L.pair a b))
                      (fun r -> L.inright (L.app loop r))))) in
      let step =
        L.rlam (fun loop r1 ->
            L.lam (fun r2 ->
                L.lam (fun _ ->
                    X.appp amb
                      (L.lam (fun _ ->
                           L.case (L.app r1 L.unit)
                             (fun a -> L.inright (X.app2 pair_left a r2))
                             (fun r1 -> L.inright (X.app2 loop r1 r2))))
                      (L.lam (fun _ ->
                           L.case (L.app r2 L.unit)
                             (fun b -> L.inright (X.app2 pair_right b r1))
                             (fun r2 -> L.inright (X.app2 loop r1 r2))))))) in
      L.lam (fun t1_t2 ->
          X.app2 step
            (L.app (L.left t1_t2) L.unit)
            (L.app (L.right t1_t2) L.unit))

    let par_op =
      L.lam (fun x -> L.app (par (X.op "amb")) x)

    let ops = [
        ("yield", (false, mreturn yield_op));
        ("atomic", (false, mreturn atomic_op));
        ("par", (false, mreturn par_op))
      ]
  end

module type PMONAD =
  functor (L : LANG) -> MONAD with type exp = L.exp

module Extend(TT : PMONAD)(L : LANG) =
  struct
    module X = Ext(L)
    module T = TT(L)

    type exp = L.exp

    let lift1 f e =
      T.mlet e (fun v -> T.mreturn (f v))

    let lift2 f e1 e2 =
      T.mlet e1 (fun v1 ->
          T.mlet e2 (fun v2 ->
              T.mreturn (f v1 v2)))

    let unit = T.mreturn L.unit
    let int k = T.mreturn (L.int k)
    let string s = T.mreturn (L.string s)

    let pair = lift2 L.pair
    let left = lift1 L.left
    let right = lift1 L.right

    let inleft = lift1 L.inleft
    let inright = lift1 L.inright

    let case e f1 f2 =
      T.mlet e (fun v ->
          L.case v
            (fun v1 -> f1 (T.mreturn v1))
            (fun v2 -> f2 (T.mreturn v2)))

    let elet e f =
      T.mlet e (fun v ->
          L.elet v (fun v ->
              f (T.mreturn v)))

    let lam f =
      T.mreturn (L.lam (fun v -> f (T.mreturn v)))

    let rlam f =
      T.mreturn (L.rlam (fun v1 v2 -> f (T.mreturn v1) (T.mreturn v2)))

    let app e1 e2 =
      T.mlet e1 (fun v1 ->
          T.mlet e2 (fun v2 ->
              L.app v1 v2))

    let nil = T.mreturn L.nil
    let cons = lift2 L.cons

    let fold nil cons l =
      T.mlet cons (fun cons ->
          T.mlet l (fun l ->
              L.fold nil
                (L.lam (fun a ->
                     L.lam (fun sb ->
                         T.mlet (L.app cons a) (fun cons_a ->
                             T.mlet sb (fun sb ->
                                 L.app cons_a sb)))))
                l))

    type result = L.result

    let show e =
      L.show (T.mshow e)

    let lift_op (name, (ty, op)) =
      (name,
       (ty,
        T.mreturn
          (if ty
           then X.compose (L.lam T.mreturn) op
           else op)))

    let ops =
      List.append T.ops
        (List.map lift_op L.ops)
  end

module Compose(PT : PMONAD)(PS : PMONAD)(L : LANG) =
  struct
    module SL  = Extend(PS)(L)
    module XSL = Ext(SL)
    module S   = PS(L)
    module T   = PT(SL)

    type exp = L.exp

    let mreturn a =
      T.mreturn (S.mreturn a)

    let mlet sta f =
      T.mlet sta (fun sa -> S.mlet sa f)

    let mshow e =
      S.mshow (T.mshow e)

    let lift_op (name, (ty, op)) =
      (name,
       (ty,
        T.mreturn
          (if ty
           then XSL.compose (SL.lam T.mreturn) op
           else op)))

    let ops =
      List.append T.ops
        (List.map lift_op S.ops)
  end

module type EFFECT_LANG =
  sig
    include LANG
    val leteff : (exp -> exp) -> (exp -> (exp -> exp) -> exp) -> exp -> exp
  end

module EffectLang(L : LANG) =
  struct
    module X = Ext(L)

    type exp = (L.exp -> L.exp) -> (L.exp -> (L.exp -> L.exp) -> L.exp) -> L.exp

    let lift0 e sreturn slet =
      sreturn e

    let lift1 f e sreturn slet =
      slet (e sreturn slet) (fun x ->
          sreturn (f x))

    let lift2 f e1 e2 sreturn slet =
      slet (e1 sreturn slet) (fun x ->
          slet (e2 sreturn slet) (fun y ->
              sreturn (f x y)))

    let unit = lift0 L.unit
    let int k = lift0 (L.int k)
    let string s = lift0 (L.string s)

    let pair = lift2 L.pair
    let left = lift1 L.left
    let right = lift1 L.right

    let inleft = lift1 L.inleft
    let inright = lift1 L.inright

    let case e f1 f2 sreturn slet =
      slet (e sreturn slet) (fun e ->
          L.case e
            (fun e1 -> f1 (lift0 e1) sreturn slet)
            (fun e2 -> f2 (lift0 e2) sreturn slet))

    let elet e f sreturn slet =
      slet (e sreturn slet) (fun e ->
          L.elet e (fun e -> f (lift0 e) sreturn slet))

    let lam f sreturn slet =
      sreturn (L.lam (fun e -> f (lift0 e) sreturn slet))

    let rlam f sreturn slet =
      sreturn (L.rlam (fun self e -> f (lift0 self) (lift0 e) sreturn slet))

    let app e1 e2 sreturn slet =
      slet (e1 sreturn slet) (fun x ->
          slet (e2 sreturn slet) (fun y ->
              L.app x y))

    let nil = lift0 L.nil
    let cons = lift2 L.cons

    let fold nil cons l sreturn slet =
      slet (cons sreturn slet)
        (fun cons ->
          slet (l sreturn slet) (fun l ->
              L.fold (nil sreturn slet)
                (L.lam (fun a ->
                     L.lam (fun sb ->
                         slet (L.app cons a) (fun cons_a ->
                             slet sb (fun sb ->
                                 L.app cons_a sb)))))
                l))

    let leteff treturn tlet e sreturn slet =
      let streturn a =
        treturn (lift0 a) sreturn slet in
      let stlet sta f =
        slet sta (fun ta ->
            tlet (lift0 ta) (app (lift0 (L.lam f)))
              sreturn slet) in
      e streturn stlet

    type result = L.result

    let show e =
      let id_return a = a in
      let id_let ma f = L.app (L.lam f) ma in
      L.show (e id_return id_let)

    let lift_op (name, (ty, op)) =
      (name,
       (ty,
        fun sreturn slet ->
        sreturn (L.lam (fun v -> sreturn (L.app op v)))))

    let ops =
      List.map lift_op L.ops
  end

module ReifyReflectOps(L : LANG) =
  struct
    module X = Ext(L)

    let raise_op =
      L.lam (fun _ ->
          L.app (X.op "reflect_exception")
            (L.inright L.unit))

    let exception_return a =
      L.inleft a

    let write =
      L.lam (fun s ->
          L.app (X.op "reflect_writer")
            (L.pair (exception_return L.unit) s))

    let fail =
      L.lam (fun _ -> L.app (X.op "reflect_list") L.nil)

    let amb =
      L.lam (fun t1_t2 ->
          L.app (X.op "reflect_list")
            (X.appp (X.op "append")
               (L.app (X.op "reify_list") (L.left t1_t2))
               (L.app (X.op "reify_list") (L.right t1_t2))))

    let pick =
      L.lam (fun nums ->
          (L.app
             (L.fold fail
                (L.lam (fun k ->
                     L.lam (fun t ->
                         L.lam (fun _ ->
                             X.appp amb (L.lam (fun _ -> k)) t))))
                nums)
             L.unit))

    let handle =
      L.lam (fun t1_t2 ->
          L.case (L.app (X.op "reify_exception") (L.left t1_t2))
            (fun a -> L.app (X.op "reflect_exception") (L.inleft a))
            (fun _ -> L.app (L.right t1_t2) L.unit))
  end

module Examples01(L : LANG) =
  struct
    module X = Ext(L)

    let ex01 =
      L.show
        (X.appp (X.op "handle")
           (L.lam (fun _ ->
                L.elet
                  (L.app (X.op "pick")
                     (X.list [L.int 1; L.int 2; L.int 3; L.int 4; L.int 5]))
                  (fun a ->
                    X.seq (L.app (X.op "write") (L.string "a="))
                      (X.seq (L.app (X.op "write") (L.app (X.op "int_to_string") a))
                         (X.seq
                            (L.case (X.appp (X.op "equals") (L.int 9)
                                       (X.appp (X.op "times") a a))
                               (fun _ -> X.seq (L.app (X.op "write") (L.string "!"))
                                           (L.app (X.op "raise") L.unit))
                               (fun _ -> L.app (X.op "write") (L.string "ok")))
                            (X.appp (X.op "times") (L.int 10) a))))))
           (L.lam (fun _ ->
                X.seq (L.app (X.op "write") (L.string "H"))
                  (L.case (L.app (X.op "pick") (X.list [X.etrue; X.efalse]))
                     (fun _ -> X.seq (L.app (X.op "write") (L.string "yes")) (L.int 42))
                     (fun _ -> L.app (X.op "raise") L.unit)))))
  end

module Examples01R(L : LANG) =
  struct
    module X = Ext(L)
    module RR = ReifyReflectOps(L)

    let ex01 =
      L.show
        (X.appp RR.handle
           (L.lam (fun _ ->
                L.elet
                  (L.app RR.pick (X.list [L.int 1; L.int 2; L.int 3; L.int 4; L.int 5]))
                  (fun a ->
                    X.seq (L.app RR.write (L.string "a="))
                      (X.seq (L.app RR.write (L.app (X.op "int_to_string") a))
                         (X.seq
                            (L.case (X.appp (X.op "equals") (L.int 9)
                                       (X.appp (X.op "times") a a))
                               (fun _ -> X.seq (L.app RR.write (L.string "!"))
                                           (L.app RR.raise_op L.unit))
                               (fun _ -> L.app RR.write (L.string "ok")))
                            (X.appp (X.op "times") (L.int 10) a))))))
           (L.lam (fun _ ->
                X.seq (L.app RR.write (L.string "H"))
                  (L.case (X.appp RR.amb
                             (L.lam (fun _ -> X.etrue))
                             (L.lam (fun _ -> X.efalse)))
                     (fun _ -> X.seq (L.app RR.write (L.string "yes")) (L.int 42))
                     (fun _ -> L.app RR.raise_op L.unit)))))
  end

module Examples01E(L : EFFECT_LANG) =
  struct
    module X = Ext(L)
    module ListM = ListMonad(L)
    module WriterM = WriterMonad(L)
    module ExceptionM = ExceptionMonad(L)

    let ex01 =
      L.show
        (L.elet ListM.pick_op (fun pick ->
             L.leteff ListM.mreturn ListM.mlet
               (L.elet WriterM.write_op (fun write ->
                    L.elet (X.compose (L.lam WriterM.mreturn) pick) (fun pick ->
                        L.leteff WriterM.mreturn WriterM.mlet
                          (L.elet ExceptionM.raise_op (fun raise ->
                               L.elet ExceptionM.handle_op (fun handle ->
                                   L.elet (X.compose (L.lam ExceptionM.mreturn) pick) (fun pick ->
                                       L.elet (X.compose (L.lam ExceptionM.mreturn) write) (fun write ->
                                           L.leteff ExceptionM.mreturn ExceptionM.mlet
                                             (X.appp handle
                                                (L.lam (fun u ->
                                                     L.elet
                                                       (L.app pick
                                                          (X.list [L.int 1; L.int 2; L.int 3; L.int 4; L.int 5])) (fun a ->
                                                         X.seq (L.app write (L.string "a="))
                                                           (X.seq (L.app write (L.app (X.op "int_to_string") a))
                                                              (X.seq
                                                                 (L.case (X.appp (X.op "equals") (L.int 9)
                                                                            (X.appp (X.op "times") a a))
                                                                    (fun u -> X.seq (L.app write (L.string "!"))
                                                                                (L.app raise L.unit))
                                                                    (fun u -> L.app write (L.string "ok")))
                                                                 (X.appp (X.op "times") (L.int 10) a))))))
                                                (L.lam (fun u ->
                                                     X.seq (L.app write (L.string "H"))
                                                       (L.case (L.app pick (X.list [X.etrue; X.efalse]))
                                                          (fun u -> X.seq (L.app write (L.string "yes")) (L.int 42))
                                                          (fun u -> L.app raise L.unit)))))))))))))))
  end

module Examples02(L : LANG) =
  struct
    module X = Ext(L)

    let ex01 =
      let fetch =
        L.lam (fun _ ->
            L.app (X.op "yield") (X.op "get")) in
      let store =
        L.lam (fun e ->
            L.app (X.op "yield")
              (L.lam (fun _ -> L.app (X.op "set") e))) in
      L.show
        (X.appp (X.op "par")
           (L.lam (fun _ ->
                L.app store (L.int 3)))
           (L.lam (fun _ ->
                L.app store
                  (X.appp (X.op "plus") (L.int 1) (L.app fetch L.unit)))))

    let ex02 =
      let fetch =
        L.lam (fun _ ->
            L.app (X.op "yield") (X.op "get")) in
      let store =
        L.lam (fun e ->
            L.app (X.op "yield")
              (L.lam (fun _ -> L.app (X.op "set") e))) in
      L.show
        (X.appp (X.op "par")
           (L.lam (fun _ ->
                L.app (X.op "atomic")
                  (L.lam (fun _ ->
                       L.app store (L.int 3)))))
           (L.lam (fun _ ->
                L.app (X.op "atomic")
                  (L.lam (fun _ ->
                       L.app store
                         (X.appp (X.op "plus") (L.int 1) (L.app fetch L.unit)))))))
  end

module Examples02E(L : EFFECT_LANG) =
  struct
    module X = Ext(L)
    module ListM = ListMonad(L)
    module StateM = StateMonad(L)
    module ResumptionM = ResumptionMonad(L)

    let ex01 =
      L.show
        (L.elet ListM.amb_op (fun amb ->
             L.leteff ListM.mreturn ListM.mlet
               (L.elet StateM.get_op (fun get ->
                    L.elet StateM.set_op (fun set ->
                        StateM.mshow
                          (L.leteff StateM.mreturn StateM.mlet
                             (L.elet (ResumptionM.par amb) (fun par ->
                                  L.elet ResumptionM.yield_op (fun yield ->
                                      L.elet (X.compose (L.lam ResumptionM.mreturn) get) (fun get ->
                                          L.elet (X.compose (L.lam ResumptionM.mreturn) set) (fun set ->
                                              ResumptionM.mshow
                                                (L.leteff ResumptionM.mreturn ResumptionM.mlet
                                                   (L.elet (StateM.fetch_op yield get) (fun fetch ->
                                                        L.elet (StateM.store_op yield set) (fun store ->
                                                            X.appp par
                                                              (L.lam (fun u ->
                                                                   L.app store (L.int 3)))
                                                              (L.lam (fun u ->
                                                                   L.app store
                                                                     (X.appp (X.op "plus") (L.int 1)
                                                                        (L.app fetch L.unit)))))))))))))))))))

    let ex02 =
      L.show
        (L.elet ListM.amb_op (fun amb ->
             L.leteff ListM.mreturn ListM.mlet
               (L.elet StateM.get_op (fun get ->
                    L.elet StateM.set_op (fun set ->
                        StateM.mshow
                          (L.leteff StateM.mreturn StateM.mlet
                             (L.elet (ResumptionM.par amb) (fun par ->
                                  L.elet ResumptionM.yield_op (fun yield ->
                                      L.elet ResumptionM.atomic_op (fun atomic ->
                                          L.elet (X.compose (L.lam ResumptionM.mreturn) get) (fun get ->
                                              L.elet (X.compose (L.lam ResumptionM.mreturn) set) (fun set ->
                                                  ResumptionM.mshow
                                                    (L.leteff ResumptionM.mreturn ResumptionM.mlet
                                                       (L.elet (StateM.fetch_op yield get) (fun fetch ->
                                                            L.elet (StateM.store_op yield set) (fun store ->
                                                                X.appp par
                                                                  (L.lam (fun u ->
                                                                       L.app atomic
                                                                         (L.lam (fun u ->
                                                                              L.app store (L.int 3)))))
                                                                  (L.lam (fun u ->
                                                                       L.app atomic
                                                                         (L.lam (fun u ->
                                                                              L.app store
                                                                                (X.appp (X.op "plus") (L.int 1)
                                                                                   (L.app fetch L.unit))))))))))))))))))))))
  end

module Examples03E(L : EFFECT_LANG) =
  struct
    module X = Ext(L)
    module ListM = ListMonad(L)
    module WriterM = WriterMonad(L)

    let ex01 =
      L.show
        (L.elet ListM.amb_op (fun amb ->
             L.leteff ListM.mreturn ListM.mlet
               (X.appp amb
                  (L.lam (fun u -> L.int 1))
                  (L.lam (fun u ->
                       X.appp amb
                         (L.lam (fun u -> L.int 2))
                         (L.lam (fun u -> L.int 3)))))))

    let ex02 =
      L.show
        (L.elet ListM.amb_op (fun amb ->
             L.leteff ListM.mreturn ListM.mlet
               (L.leteff WriterM.mreturn WriterM.mlet
                  (X.appp amb
                     (L.lam (fun u -> L.int 1))
                     (L.lam (fun u ->
                          X.appp amb
                            (L.lam (fun u -> L.int 2))
                            (L.lam (fun u -> L.int 3))))))))

    let ex03 =
      L.show
        (L.elet ListM.pick_op (fun pick ->
             L.leteff ListM.mreturn ListM.mlet
               (L.elet (X.compose (L.lam WriterM.mreturn) pick) (fun pick ->
                    L.leteff WriterM.mreturn WriterM.mlet
                      (L.app pick (X.list [L.int 1; L.int 2; L.int 3]))))))

    let ex04 =
      L.show
        (L.elet (L.lam (fun v -> v)) (fun reflect ->
             L.elet
               (L.lam (fun t ->
                    L.app (L.lam ListM.mreturn) (L.app t L.unit))) (fun reify ->
                 L.leteff ListM.mreturn ListM.mlet
                   (L.elet
                      (L.lam (fun t1_t2 ->
                           L.app reflect
                             (X.appp (X.op "append")
                                (L.app reify (L.left t1_t2))
                                (L.app reify (L.right t1_t2))))) (fun amb ->
                        (X.appp amb
                           (L.lam (fun u -> L.int 1))
                           (L.lam (fun u ->
                                X.appp amb
                                  (L.lam (fun u -> L.int 2))
                                  (L.lam (fun u -> L.int 3))))))))))
  end

module ListL         = Extend(ListMonad)
module ExceptionL    = Extend(ExceptionMonad)
module ReaderL       = Extend(ReaderMonad)
module WriterL       = Extend(WriterMonad)
module StateL        = Extend(StateMonad)
module ContinuationL = Extend(ContinuationMonad)
module ResumptionL   = Extend(ResumptionMonad)

module ListM         = Compose(ListMonad)
module ExceptionM    = Compose(ExceptionMonad)
module ReaderM       = Compose(ReaderMonad)
module WriterM       = Compose(WriterMonad)
module StateM        = Compose(StateMonad)
module ContinuationM = Compose(ContinuationMonad)
module ResumptionM   = Compose(ResumptionMonad)

module L = Lang
module Id = IdentityMonad
module Language(M : PMONAD) = Extend(M)(L)

module Ex01L = Examples01(ExceptionL(WriterL(ListL(L))))
module Ex01M = Examples01(Language(ExceptionM(WriterM(ListM(Id)))))

module Ex01LR = Examples01R(ExceptionL(WriterL(ListL(L))))
module Ex01MR = Examples01R(Language(ExceptionM(WriterM(ListM(Id)))))

module Ex01E = Examples01E(EffectLang(L))

module Ex02L = Examples02(ResumptionL(StateL(ListL(L))))
module Ex02M = Examples02(Language(ResumptionM(StateM(ListM(Id)))))
module Ex02E = Examples02E(EffectLang(L))

module Ex03E = Examples03E(EffectLang(L))

let ex01_01L  = Ex01L.ex01
let ex01_01M  = Ex01M.ex01
let ex01_01LR = Ex01LR.ex01
let ex01_01MR = Ex01MR.ex01
let ex01_01E  = Ex01E.ex01

let ex02_01L = Ex02L.ex01
let ex02_01M = Ex02M.ex01
let ex02_01E = Ex02E.ex01

let ex02_02L = Ex02L.ex02
let ex02_02M = Ex02M.ex02
let ex02_02E = Ex02E.ex02

let ex03_01E = Ex03E.ex01
let ex03_02E = Ex03E.ex02
let ex03_03E = Ex03E.ex03
let ex03_04E = Ex03E.ex04

;;
