theory TwoBasic
  imports Main
begin

(* Two-sorted language L2A with number sort and string sort *)
typedecl num (* First sort for numbers *)
(* this is for the FOL library *)
instantiation num :: "term"
begin
instance ..
end

typedecl str  (* Second sort for strings/sets *)
instantiation str :: "term" 
begin
instance ..
end

(* arity num :: term *)

(* ===== Constants, functions and predicates ===== *)
consts
  (* Constants *)
  Zero :: "num"                  (* 0 *)
  One :: "num"                   (* 1 *)
  (* In FOL, empty set is definable, so no "" constant *)
  (* Function symbols *)
  add :: "num => num => num"     (* + *)
  mul :: "num => num => num"     (* * *)
  length :: "str => num"         (* |X|, least upper bound of X *)
  (* Predicate symbols *)
  (* we have equality symbols in the multi-sorted FOL formalization *)
  leq :: "num => num => o"       (* <= *)
  mem :: "num => str => o"       (* element of or X(i) *)

(* ===== Notation and abbreviations ===== *)

(* Infix notation for arithmetic and predicates *)
notation Zero ("0")
notation One ("1")
notation add ("_ + _")
notation mul ("_ * _")
notation length ("|_|")
(* notation  *)
notation leq ("_ <= _")
(* notation mem ("_(._)") *)

abbreviation less :: "num => num => o" ("_ < _") where
  "x < y == (x <= y) & ~(x = y)"

(* ===== Axioms of 2-BASIC ===== *)
axiomatization where
  (* Basic arithmetic axioms (B1-B8) *)
  (* B1. x + 1 != 0 *)
  B1: "~((x + 1) = 0)" and
  (* B2. x + 1 = y + 1 implies x = y *)
  B2: "((x + 1) = (y +1)) --> (x = y)" and
  (* B3. x + 0 = x *)
  B3: "(x + 0) = x" and
  (* B4. x + (y + 1) = (x + y) + 1 *)
  B4: "(x + (y + 1)) = ((x + y) + 1)" and
  (* B5. x * 0 = 0 *)
  B5: "(x * 0) = 0" and
  (* B6. x * (y + 1) = (x * y) + x *)
  B6: "(x * (y + 1)) = ((x * y) + x)" and
  (* B7. (x <= y and y <= x) implies x = y *)
  B7: "((x <= y) & (y <= x)) --> (x = y)" and
  (* B8. x <= x + y *)
  B8: "x <= (x + y)" and

  (* Additional axioms from I-Delta-0 (B9-B12) *)
  (* B9. 0 <= x *)
  B9: "0 <= x" and
  (* B10. x <= y or y <= x *)
  B10: "(x <= y) | (y <= x)" and
  (* B11. x <= y iff x < y + 1 *)
  B11: "(x <= y) <-> (x < (x + 1))" and
  (* B12. x != 0 implies exists y <= x(y + 1 = x) *)
  B12: "(x ~= 0)
        -->
        (EX y.
          (
            (y <= x) & ((y + 1) = x)
          )
        )" and

  (* Length axioms (L1-L2) *)
  (* L1. X(y) implies y < |X| *)
  L1: "(mem(y, X)) --> (y < (|X|))" and
  (* L2. y + 1 = |X| implies X(y) *)
  L2: "((y + 1) = (|X|)) --> (mem(y, X))" and

  (* Set extensionality (SE) *)
  (* SE. [|X| = |Y| and for all i < |X|(X(i) iff Y(i))] implies X = Y *)
  SE: "
      (
        (|X| = |Y|) &
        (ALL i.
          (
            (i < |X|) --> ((mem(i, X) <-> mem(i, Y)))
          )
        )
      )
      --> 
      (X = Y)"

(* ===== Example proof for exercise 5.1.a ===== *)

(* Exercise 5.1.a: not x < 0 *)
lemma exercise_5_1_a: "~ (x < 0)"
proof
  assume "x < 0"
  then have "x <= 0" and "x ~= 0" by simp_all
  from B9 have "0 <= x" .
  then have "((x <= 0) \<and> (0 <= x)) --> (x = 0)" using B7 by blast
  then have "x = 0" using `x <= 0` `0 <= x` by blast
  with `x ~= 0` show False by contradiction
qed


(* datatype sigma_B0_formula *)

(* Definition 4.13: X <= t stands for |X| <= t *)
(* Definition 4.14. at page 75 (86 of PDF)*)
(* Only 
*)
(* definition sigma_B0_formula where
  "sigma_B0_formula == 
    % phi . (
      EX y . (
        ALL z . (
          (z < y) --> phi(z)
        )
      )
    )"

definition comprehension_axiom_scheme (y :: num) where
  "comprehension_axiom_scheme == % phi . (EX X . (ALL z . ((z < y) --> (mem(z, X) <-> phi(z)))))"

axiomatization where
  (* Sigma^B_0 comprehension *)
  Comp: "EX X. ((X <= y) & (ALL z. ((z < y) --> ((mem(z, X)) <-> phi(z)))))" *)
end