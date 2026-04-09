From FOL Require Import ArithmeticalHierarchySyntactic.
From FOL Require Import FullSyntax Arithmetics.
Import FOL.PA.
Require Import List.
From FOL.Proofmode Require Import Theories ProofMode Hoas.


(* this will be different for V0 *)
Existing Instance PA_preds_signature.
Existing Instance PA_funcs_signature.
Definition one := σ zero.

Section WithPeirce.
Context {peirce : peirce}.

(* ctrl + shift + u 22a2 enter *)
(* forall: 2200 *)
Lemma refl_eq : Qeq ⊢ ∀$0 == $0.
Proof.
  fstart.
  fintros.
  fapply ax_refl.
Qed.

Open Scope PA_Notation.

Notation "'σ' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
Notation "x '⊕' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.
Definition leq a b := (∃' k, a ⊕ k == b)%hoas.
Infix "≤" := leq (at level 40).

(* Warning: `t` cannot contain occurences of 'x' ($0),
but I don't know how to enforce it. *)  
Inductive Delta0 : form -> Prop :=
| d0_false : Delta0 falsity
| d0_atom P v : Delta0 ((atom P v): form)
| d0_bin op (phi1 phi2: form) :
    Delta0 phi1 ->
    Delta0 phi2 ->
    Delta0 (bin op phi1 phi2)
| d0_bdEx t (phi1: form) :
    Delta0 phi1 ->
    Delta0 (<< ∃'x, x ≤ t ∧ phi1)
| d0_bdAll t (phi1 : form):
    Delta0 phi1 ->
    Delta0 (<< ∀'x, x ≤ t → phi1).

(* B1. x + 1 ≠ 0 *)
Definition B1 : form := << ∀'x, ¬ ( (x ⊕ one) == zero ).

(* B2. x + 1 = y + 1 → x = y *)
Definition B2 : form := << ∀'x y, ( (x ⊕ one) == (y ⊕ one) → x == y ).

(* B3. ∀x, x ⊕ 0 = x *)
(* Definition B3 : form :=
  << ∀'x, (x ⊕ zero) == x. *)
Definition B3 : form := ∀ ($0 ⊕ zero == $0).

(* B4. ∀x y, x ⊕ σ y = σ (x ⊕ y) *)
Definition B4 : form :=
  << ∀'x y, (x ⊕ σ y) == σ (x ⊕ y).

(* B5. ∀x, x ⊗ 0 = 0 *)
Definition B5 : form :=
  << ∀'x, (x ⊗ zero) == zero.

(* B6. ∀x y, x ⊗ (y ⊕ 1) = (x ⊗ y) ⊕ x *)
Definition B6 : form :=
  << ∀'x y, (x ⊗ (y ⊕ one)) == ((x ⊗ y) ⊕ x).

(* B7. ∀x y, (x ≤ y ∧ y ≤ x) → x = y *)
Definition B7 : form :=
  << ∀'x y, ((x ≤ y) ∧ (y ≤ x)) → x == y.

(* B8. ∀x y, x ≤ x ⊕ y *)
Definition B8 : form :=
  << ∀'x y, x ≤ (x ⊕ y).

(* C. 0 ⊕ 1 = 1 *)
Definition C : form :=
  (zero ⊕ one) == one.
Definition Beq_axioms : list form := B1 :: B2 :: B3 :: B4 :: B5 :: B6 :: B7 :: B8 :: C :: EQ.

Inductive Delta0eq : form -> Prop :=
  ax_B phi : In phi Beq_axioms -> Delta0eq phi
| ind phi (_ : Delta0 phi): Delta0eq (ax_induction phi).

Ltac custom_fold ::= fold ax_induction in *.
Ltac custom_unfold ::= unfold ax_induction in *.


(* axioms have the correct form; see QEqLiFull.v line 24 *)
(* instance of frewrite: coq-library-fol/theories/Proofmode/DemoPA.v : https://github.com/uds-psl/coq-library-fol/blob/b967df481c13e0fa2336051105a9629e935c7eb8/theories/Proofmode/DemoPA.v#L153*)
(* ^ in the above we see that === vs == doesn't matter for us *)

Definition BEq_axioms' := 
  (ax_induction (<< Free z, ∀' x y, (((x ⊕ y) ⊕ z) == (x ⊕ (y ⊕ z)))))
  :: Beq_axioms.

(* Note: not ⊢T neither ⊩ , we need to operate in a finite fragment of the theory *)
Lemma add_assoc : BEq_axioms' ⊢ << ∀' x y z, (((x ⊕ y) ⊕ z) == (x ⊕ (y ⊕ z))).
Proof.
  unfold BEq_axioms'.
  unfold Beq_axioms.

  fintros _1 _2 _3 .
  fapply 0.
  + fintros x y.
    frewrite (B3 (x ⊕ y)).

