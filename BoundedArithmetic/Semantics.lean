import Lean

import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.Syntax
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.SimpRules
import BoundedArithmetic.Order
import BoundedArithmetic.LanguagePeano

namespace FirstOrder.Language
open BoundedFormula

open Lean Elab Tactic Command


namespace Term


@[delta0_simps] lemma realize_zero {M} [peano.Structure M] {a} {env : a → M} :
  Language.Term.realize env (0 : peano.Term a) = (0 : M) := by
  simp only [OfNat.ofNat, Zero.zero]
  simp only [peano, Term.realize_constants]
  rfl

-- it is important to define OfNat 1 as 1, not (0+1), as the later needs an axiom to
-- be asserted equal to 1.
@[delta0_simps] lemma realize_one {M} [peano.Structure M] {a} {env : a → M} :
  Term.realize env (1 : peano.Term a) = (1 : M) := by
  simp only [OfNat.ofNat, One.one]
  simp only [peano, Term.realize_constants]
  rfl

@[delta0_simps] lemma realize_add {M} [h : peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t + u) = Term.realize env t + Term.realize env u := by
  simp only [peano, HAdd.hAdd, Add.add]
  -- TODO: why the below doesn't work without @?
  rw [@Term.realize_functions_apply₂]

@[delta0_simps] lemma realize_mul {M} [peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t * u) = Term.realize env t * Term.realize env u := by
  simp only [HMul.hMul, Mul.mul]
  rw [@Term.realize_functions_apply₂]

end Term


namespace Formula

variable {L : Language} {M : Type*} [L.Structure M] {a b} {n1 n2 n3}

@[delta0_simps]
lemma realize_flip (phi : L.Formula (a ⊕ b) ) {v : (b ⊕ a) -> M}
  : phi.flip.Realize v
    <->
    phi.Realize (v ∘ Sum.swap)
  :=
by
  unfold Formula.Realize
  unfold Formula.flip
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display1 (phi : L.Formula (Vars1 n1))  {v : ((Vars1 n1) ⊕ Empty) -> M}
  : phi.display1.Realize v
    <->
    phi.Realize (v ∘ .inl)
  :=
by
  unfold Formula.Realize
  unfold Formula.display1
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display2 (phi : L.Formula (Vars2 n1 n2)) {v : ((Vars1 n1) ⊕ (Vars1 n2)) -> M}
  : phi.display2.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with | .fv1 => .inl .fv1 | .fv2 => .inr .fv1))
  :=
by
  unfold Formula.Realize
  unfold Formula.display2
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display3 (phi : L.Formula (Vars3 n1 n2 n3)) {v : ((Vars1 n1) ⊕ (Vars2 n2 n3)) -> M}
  : phi.display3.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with | .fv1 => .inl .fv1 | .fv2 => .inr .fv1 | .fv3 => .inr .fv2))
  :=
by
  unfold Formula.Realize
  unfold Formula.display3
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl




/-- `peel_iAlls' k` rewrites `(iAlls' φ).Realize` by peeling exactly
    `k` quantifiers (`realize_all; intro`). -/
syntax (name := peelIAlls) "peel_iAlls' " num : conv

-- TODO: substitute `n` with actual size of `IsEnum`'ed type
elab_rules : conv
| `(conv| peel_iAlls' $k:num) => do
  let some n := k.raw.isNatLit?
    | throwErrorAt k "peel_iAlls': expected a nonnegative integer literal"
  Conv.evalUnfold (← `(conv| unfold iAlls'))
  for _ in [:n + 1] do
    Conv.evalUnfold (← `(conv| unfold BoundedFormula.alls))
  for _ in [:n] do
    Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_all]))
    Conv.evalExt (← `(conv| ext))
  Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_relabel]))

/-- `peel_iExs' k` rewrites `(iExs' φ).Realize` by peeling exactly
    `k` quantifiers (`realize_ex; intro`). -/
syntax (name := peelIExs) "peel_iExs' " num : conv

-- TODO: substitute `n` with actual size of `IsEnum`'ed type
elab_rules : conv
| `(conv| peel_iExs' $k:num) => do
  let some n := k.raw.isNatLit?
    | throwErrorAt k "peel_iExs': expected a nonnegative integer literal"
  Conv.evalUnfold (← `(conv| unfold iExs'))
  for _ in [:n + 1] do
    Conv.evalUnfold (← `(conv| unfold BoundedFormula.exs))
  for _ in [:n] do
    Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_ex]))
    Conv.evalEnter (← `(conv| enter [1]))
    Conv.evalExt (← `(conv| ext))
  Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_relabel]))



@[delta0_simps]
lemma realize_iAlls'.Empty (phi : L.Formula (a ⊕ Empty) ) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      phi.Realize
        (Sum.elim v Empty.elim)
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 0

  constructor <;>
    (
      intro h;
      convert h;
      funext;
      rename_i x;
      cases x;
      simp only [Sum.elim_inl, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        Function.comp_apply, Sum.map_inl, id_eq]
      apply Empty.elim; assumption
    )

-- TODO: IT SHOULD HOLD DEFINITIONALLY?... but I couldn't prove without funext
@[delta0_simps]
lemma realize_iAlls'.Vars1 (phi : L.Formula (a ⊕ Vars1 n1) ) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 1
    -- unfold IsEnum.toIdx instIsEnumVars1; dsimp only
  -- conv =>
  --   rhs; rhs; arg 2; arg 2; intro; dsimp only
  constructor <;>
    (
      intro h a;
      specialize h a;
      convert h;
      funext;
      rename_i x;
      cases x;
    ) <;>
    simp [Fin.snoc]

@[delta0_simps]
lemma realize_iAlls'.Vars2 (phi : L.Formula (a ⊕ Vars2 n1 n2)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x y : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x | .fv2 => y))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 2

  constructor <;>
    (
      intro h a;
      specialize h a;
      convert h;
      funext;
      rename_i x;
      cases' x with x_l x_r;
    ) <;> (try cases' x_r with x_rl x_rr)
      <;> simp [Fin.snoc, IsEnum.toIdx.Vars2]

@[delta0_simps]
lemma realize_iAlls'.Vars3 (phi : L.Formula (a ⊕ Vars3 n1 n2 n3)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x y z : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x | .fv2 => y | .fv3 => z))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 3

  constructor <;>
    (
      intro h a;
      specialize h a;
      convert h;
      funext;
      rename_i x;
      cases' x with x_l x_r;
    ) <;> (try cases' x_r with x_rl x_rr)
      <;> simp [Fin.snoc, IsEnum.toIdx.Vars3]

@[delta0_simps]
lemma realize_iExs'.Vars1 (phi : L.Formula (a ⊕ Vars1 n1) ) {v : a -> M}
  : phi.iExs'.Realize v
    <->
      ∃ x : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iExs' 1
  constructor <;>
    (
      intro h;
      obtain ⟨x, hx⟩ := h;
      exists x
      convert hx;
      funext;
      rename_i x;
      cases x;
    ) <;>
    simp [Fin.snoc]


section IsOrdered
variable {M : Type*} [peano.Structure M]

-- @[irreducible] def iBdEx' {α n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
--   let bd := (var (.inl (Sum.inr (.fv1)))).le $ bdTerm.relabel (Sum.map .inl id)
--   iExs' $ bd ⊓ φ
@[delta0_simps]
theorem realize_iBdEx' {t : peano.Term (a ⊕ Fin 0)} (phi : peano.Formula (a ⊕ Vars1 n1)) {v : a -> M}
  : (iBdEx' t phi).Realize v
    <->
    ∃ x : M, (x <= (t.realize (Sum.elim v Fin.elim0)) ∧ phi.Realize (Sum.elim v (fun _ => x))) :=
by
  unfold iBdEx'
  rw [realize_iExs'.Vars1]
  conv =>
    lhs; rhs; intro;
    rw [realize_inf]
    conv =>
      lhs;
      change BoundedFormula.Realize _ _ _
      rw [Term.realize_le]
      simp only [peano.instLEOfStructure, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
        Term.realize_relabel]
    conv =>
      rhs;
      simp only

  conv =>
    rhs
    rhs; intro;
    lhs;

  sorry


end IsOrdered

end Formula
end FirstOrder.Language
