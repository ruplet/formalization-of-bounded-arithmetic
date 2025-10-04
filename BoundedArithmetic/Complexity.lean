import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Syntax

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.Order
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Register

open FirstOrder Language

universe u
variable {L : Language} {α β : Type u} {n : Nat}

namespace FirstOrder.Language

namespace BoundedFormula.IsAtomic
variable {φ : L.BoundedFormula α n}

theorem relabelEquiv.mpr {f : α ≃ β} (h : φ.IsAtomic)
  : (φ.relabelEquiv f).IsAtomic
:=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem relabelEquiv.mp {f : α ≃ β} (h : (φ.relabelEquiv f).IsAtomic)
  : φ.IsAtomic :=
by
  unfold relabelEquiv mapTermRelEquiv at h
  simp at h
  -- dependent eliminatoin failed ;(
  -- cases h with
  sorry

@[delta0_simps]
theorem relabelEquiv {f : α ≃ β} :
  (φ.relabelEquiv f).IsAtomic <-> φ.IsAtomic :=
  ⟨relabelEquiv.mp, relabelEquiv.mpr⟩
end BoundedFormula.IsAtomic

namespace Formula.IsAtomic
open BoundedFormula

@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)}:
  phi.display1.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display1
  rw [IsAtomic.relabelEquiv]

@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)}:
  phi.display2.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display2
  rw [IsAtomic.relabelEquiv]

@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)}:
  phi.display3.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display3
  rw [IsAtomic.relabelEquiv]

end Formula.IsAtomic


namespace BoundedFormula.IsQF

@[delta0_simps]
theorem imp.mpr {L : Language} {α} {m} {φ ψ : L.BoundedFormula α m} :
    (φ.imp ψ).IsQF <-> (φ.IsQF ∧ ψ.IsQF) := by
  constructor
  · intro h
    constructor
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact pre
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact post
  · intro h
    apply IsQF.imp h.left h.right

@[delta0_simps]
theorem relabelEquiv.mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : φ.IsQF) :
  (φ.relabelEquiv f).IsQF := by
  sorry

@[delta0_simps]
theorem relabelEquiv.mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : (φ.relabelEquiv f).IsQF) :
    φ.IsQF := by
  sorry

@[delta0_simps]
theorem relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsQF <-> φ.IsQF := ⟨IsQF.relabelEquiv.mpr f, IsQF.relabelEquiv.mp f⟩

-- @[delta0_simps]
-- theorem mapTermRel {α β} {m : ℕ} {φ : peano.BoundedFormula α 0} {g : Nat -> Nat}  (ft: forall n, peano.Term (α ⊕ (Fin n)) -> peano.Term (β ⊕ Fin (g n))) (fr) (h) :
--   (φ.mapTermRel ft fr h).IsQF <-> φ.IsQF := by
--   sorry

end BoundedFormula.IsQF



-- Definition 3.7, page 36 of draft (47 of pdf)
abbrev BoundedFormula.IsOpen (formula : L.BoundedFormula α n)
  := IsQF formula
namespace BoundedFormula.IsOpen
variable {phi : L.BoundedFormula α n}

@[delta0_simps]
theorem equal (t1 t2 : L.Term (α ⊕ Fin n))
  : (t1.bdEqual t2).IsOpen :=
by
  constructor
  apply IsAtomic.equal

@[delta0_simps]
theorem imp.mpr.left {psi : _}
  : (phi.imp psi).IsOpen -> phi.IsOpen :=
by
  intro h
  -- TODO: order of constructors in IsQF should be reversed,
  -- so that `constructor` here works!
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact p

@[delta0_simps]
theorem imp.mpr.right {psi : _}
  : (phi.imp psi).IsOpen -> psi.IsOpen :=
by
  intro h
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact q

@[delta0_simps]
theorem not
  : phi.not.IsOpen <-> phi.IsOpen :=
by
  constructor <;> (unfold BoundedFormula.not; intro h)
  · exact imp.mpr.left h
  · apply IsQF.imp
    · assumption
    · exact isQF_bot

@[delta0_simps]
theorem relabelEquiv {f : α ≃ β}
  : (phi.relabelEquiv f).IsOpen <-> phi.IsOpen :=
by
  constructor <;> intro h
  · -- dependent elimination failed on 'cases h' :(((
    sorry
  · induction h with
    | falsum =>
      rw [relabelEquiv.falsum]
      exact IsQF.falsum
    | of_isAtomic h =>
      constructor
      rw [IsAtomic.relabelEquiv]
      exact h
    | imp h1 h2 h1_ih h2_ih =>
      rw [relabelEquiv.imp]
      apply IsQF.imp
      · exact h1_ih
      · exact h2_ih

end BoundedFormula.IsOpen

namespace Formula.IsOpen
open BoundedFormula.IsOpen

@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)}:
    phi.display1.IsOpen <-> phi.IsOpen := by
  unfold Formula.display1
  rw [relabelEquiv]

@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)}:
    phi.display2.IsOpen <-> phi.IsOpen := by
  unfold Formula.display2
  rw [relabelEquiv]

@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)}:
    phi.display3.IsOpen <-> phi.IsOpen := by
  unfold Formula.display3
  rw [relabelEquiv]

end Formula.IsOpen



variable {L : Language} [IsOrdered L] {a : Type u}
open BoundedFormula Formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
-- fix level of `a` to 0, because level of `Vars` was fixed to 0!
inductive BoundedFormula.IsDelta0 {a : Type}: {n : Nat} -> L.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsDelta0 phi1) (h2 : IsDelta0 phi2)
  : IsDelta0 (phi1.imp phi2)
| bdEx {n} (phi : L.Formula (a ⊕ (Vars1 n))) (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 $ iBdEx' t phi
| bdAll {n} (phi : L.Formula (a ⊕ (Vars1 n))) (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 $ iBdAll' t phi
| of_isQF {phi} (h : BoundedFormula.IsQF phi)
  : IsDelta0 phi


namespace IsDelta0

@[delta0_simps]
theorem bot {a n} : (⊥ : L.BoundedFormula a n).IsDelta0  := by
  constructor
  exact isQF_bot

@[delta0_simps]
theorem equal {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1.bdEqual t2).IsDelta0 :=
by
  constructor
  constructor
  apply IsAtomic.equal

set_option allowUnsafeReducibility true in
section
attribute [local reducible] iBdEx' iBdAll'

theorem of_open.imp {a n} {phi psi : L.BoundedFormula a n} (h : phi.IsOpen)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h
    cases h with
    | imp p q =>
      constructor
      · exact p
      · exact q
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      cases h with
      | of_isAtomic h' =>
        cases h' with
  · intro h
    apply IsDelta0.imp
    exact h.left
    exact h.right

theorem of_notfalsum.imp {a n} {phi psi : L.BoundedFormula a n} (h : psi ≠ falsum)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h'
    cases h' with
    | imp p q =>
      constructor
      · exact p
      · exact q
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      simp only [Bot.bot, ne_eq, not_true_eq_false] at h
  · intro h
    apply IsDelta0.imp
    exact h.left
    exact h.right

end


@[delta0_simps]
theorem neq {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1 ≠' t2).IsDelta0 :=
by
  constructor
  apply equal
  apply bot

theorem of_open.not {a n} {phi : L.BoundedFormula a n} (h : phi.IsOpen)
  : phi.not.IsDelta0 <-> phi.IsDelta0 :=
by
  unfold BoundedFormula.not
  rw [of_open.imp h]
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · exact IsDelta0.bot

@[delta0_simps]
theorem relabelEquiv {a b} (phi : peano.Formula a) {g : a ≃ b}:
  (phi.relabelEquiv g).IsDelta0 <-> BoundedFormula.IsDelta0 phi :=
by
  cases phi with
  | falsum =>
    apply Iff.intro <;> (intro; constructor; constructor)
  | equal =>
    apply Iff.intro <;> (intro; constructor; constructor; constructor)
  | imp p q =>
    sorry
  | rel =>
    constructor <;> (intro; constructor; constructor; constructor)
  -- | ex => sorry
  | all => sorry


theorem display1 {n} (phi : peano.Formula (Vars1 n)) :
  phi.display1.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

theorem display2 {n1 n2} (phi : peano.Formula (Vars2 n1 n2)) :
  phi.display2.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

theorem display3 {n1 n2 n3} (phi : peano.Formula (Vars3 n1 n2 n3)) :
  phi.display3.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

theorem flip {a b} (phi : peano.Formula (a ⊕ b)) :
  phi.flip.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

end IsDelta0




-- only bounded number quantifiers allowed. and free string vars.
-- p. 82 of pdf of Logical Foundatoin release
inductive BoundedFormula.IsSigma0B {a : Type} : {n : Nat} -> zambella.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsSigma0B phi1) (h2 : IsSigma0B phi2)
  : IsSigma0B (phi1.imp phi2)
| bdEx
  {n}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdEx' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ .fv1]) ⊓ phi)
-- TODO: WHICH ONE IS REDUNDANT?
| bdAll
  {n}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdAll' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ .fv1]) ⊓ phi)
| bdAllLt
  {n}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdAllLt' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ .fv1]) ⊓ phi)

| of_isQF {phi} (h : IsQF phi) : IsSigma0B phi

namespace Sigma0B

@[delta0_simps]
theorem relabelEquiv {a b} {g : a ≃ b} (phi : zambella.Formula a):
  (phi.relabelEquiv g).IsSigma0B <-> phi.IsSigma0B :=
by
  sorry

end Sigma0B



syntax (name := simp_complexity) "simp_complexity" " at " (ppSpace ident)? : tactic

macro_rules
| `(tactic| simp_complexity at $h:ident) =>
  `(tactic|
  conv at $h =>
    conv =>
      lhs
      simp only [delta0_simps]
    -- this has to work! the `IsOpen` goal has to reduce to `True`.
    rw [forall_const]
  )


end FirstOrder.Language
