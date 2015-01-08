(* Chapter 15: Extracting ML from Coq *)

(* basic extraction *)
Require Import SfLib ImpCEvalFun.

(* Can open `impl1.ml` after stepping past the next line *)
Extraction "imp1.ml" ceval_step.


(* Controlling extraction of specific types *)
Extract Inductive bool => "bool" ["true" "false"]. (* enumeration types *)
(* types that require parameters on their constructors *)
(* type, [constructors], recursor *)
Extract Inductive nat => "int" ["0" "(fun x -> x + 1)"]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
(* extract constants to ocaml operators *)
Extract Constant plus    => "( + )".
Extract Constant mult    => "( * )".
Extract Constant beq_nat => "( = )".

Extraction "imp2.ml" ceval_step.
(* imp2.ml uses the ocaml version of bool and int (nat) *)

(*
   The extracted version of ceval_step in imp2 uses the recursor,
   rather than directly coding a recursive function

   I like that.
*)



(* Complete example *)
Require Import Ascii String.
Extract Inductive ascii => char
  [ "(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
  ]
  "(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'001'".
Extract Constant shift => "fun b c -> Char.chr (((Char.code c) lsl 1) land 26 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".

Extract Inductive sumbool => "bool" ["true" "false"].
Require Import Imp ImpParser.
Extraction "imp.ml" empty_state ceval_step parse.
(*
   ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
   ./impdriver
(*

(* Discussion *)
(*
   "The extracted program can be viewed as a 'certified' Imp interpreter"

   IMO: But, I could just say to someone that I extracted a certified program.
        separating the coq logic/runtime system from the things it produces is
        just no good.
*)