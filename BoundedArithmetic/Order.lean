import Mathlib.ModelTheory.Order

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.Syntax

namespace FirstOrder.Language.Formula

open Language BoundedFormula

section IsOrdered
universe u
variable {L : Language} [IsOrdered L] {α : Type u}

-- there is relabel_sumInl
@[irreducible] def iBdEx' {α} {β} [HasDisplayed β] (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (HasDisplayed.fv)))).le $ bdTerm.relabel (Sum.map .inl id)

  iExs' $ bd ⊓ φ

@[irreducible] def iBdAll' {α} {β} [HasDisplayed β] (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (HasDisplayed.fv)))).le $ bdTerm.relabel (Sum.map .inl id)
  iAlls' $ bd ⟹ φ

end IsOrdered

end FirstOrder.Language.Formula

-- #check ∃ x < 7
-- #check FirstOrder.Language.Formula.iExs'
-- def iBdExComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
--   iExs' (
--     BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
--     ⊓ φ
--   )

-- def iBdExUniqueComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
--   iExsUniqueComputable BoundedFormula.DisplayedFV1.equivFin1 (
--     BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
--     ⊓ φ
--   )

-- -- THIS IS FULL GENERALITY!
-- -- Supports: ∃x ≤ t1() ∧ ∃y ≤ t2(x) ∧ ∃z ≤ t3(x, y) ∧ ... φ(x,y,z,⋯)
-- -- @[simp] def iBdExsComputableAux {α} : {k : Nat} -> (bdTerms : (i : Fin k) -> peano.Term ((α ⊕ Fin i) ⊕ Fin 0)) -> (φ : peano.Formula (α ⊕ Fin k)) -> peano.Formula α
-- -- | 0, _, φ => sorry
-- -- | k + 1, bdTerms, φ => sorry

-- @[simp] def iBdAllComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
--   iAllsComputable BoundedFormula.DisplayedFV1.equivFin1 (
--     BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
--     ⟹ φ
--   )



-- @[simp] def boundedEx {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
--   -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
--   -- `&(Fin.last n)` lifts `n` into Term.var; this denotes just `x`
--   -- `t.relabel...` lifts `t` from lv `n` to lv `n + 1`
--   ((BoundedFormula.rel PeanoRel.leq ![
--     (&(Fin.last n)),
--     (t.relabel $ Sum.map id (Fin.succEmb n))
--     ]
--   ) ⊓ f).ex


-- @[simp] def boundedAll {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
--   ((BoundedFormula.rel PeanoRel.leq ![
--     (&(Fin.last n)),
--     (t.relabel $ Sum.map id (Fin.succEmb n))
--     ]
--   ) ⟹ f).all

-- @[simp] def boundedExUnique {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
--   -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
--   -- `&(Fin.last n)` lifts `n` into Term.var; this denotes just `x`
--   -- `t.relabel...` lifts `t` from lv `n` to lv `n + 1`
--   ((BoundedFormula.rel PeanoRel.leq ![
--     (&(Fin.last n)),
--     (t.relabel $ Sum.map id (Fin.succEmb n))
--     ]
--   ) ⊓ f ⊓ (forall y, y<=t -> phi(y) -> y = x0 )).ex



-- -- the below is from BinderPredicates.lean. use the below to find it
-- -- #check ∃ x < 7, x < x


-- open Lean

-- /-
-- The syntax category of binder predicates contains predicates like `> 0`, `∈ s`, etc.
-- (`: t` should not be a binder predicate because it would clash with the built-in syntax for ∀/∃.)
-- -/
-- declare_syntax_cat binderPredFirstOrder

-- /-
-- `satisfies_binder_pred% t pred` expands to a proposition expressing that `t` satisfies `pred`.
-- -/
-- syntax "satisfies_binder_pred% " term:max binderPredFirstOrder : term

-- -- Extend ∀ and ∃ to binder predicates.

-- /--
-- The notation `∃ x < 2, p x` is shorthand for `∃ x, x < 2 ∧ p x`,
-- and similarly for other binary operators.
-- -/
-- syntax "∃' " binderIdent binderPredFirstOrder ", " term : term
-- /--
-- The notation `∀ x < 2, p x` is shorthand for `∀ x, x < 2 → p x`,
-- and similarly for other binary operators.
-- -/
-- syntax "∀' " binderIdent binderPredFirstOrder ", " term : term

-- @[inherit_doc] scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex

-- macro_rules
--   | `(∃' $x:ident $pred:binderPredFirstOrder, $p) =>
--     `(∃ $x:ident, satisfies_binder_pred% $x $pred ∧ $p)
--   | `(∃' _ $pred:binderPredFirstOrder, $p) =>
--     `(∃ x, satisfies_binder_pred% x $pred ∧ $p)

-- macro_rules
--   | `(∀' $x:ident $pred:binderPredFirstOrder, $p) =>
--     `(∀' $x:ident, satisfies_binder_pred% $x $pred → $p)
--   | `(∀' _ $pred:binderPredFirstOrder, $p) =>
--     `(∀' x, satisfies_binder_pred% x $pred → $p)

-- /-- Declare `∃ x > y, ...` as syntax for `∃ x, x > y ∧ ...` -/
-- binder_predicate x " > " y:term => `($x > $y)
-- /-- Declare `∃ x ≥ y, ...` as syntax for `∃ x, x ≥ y ∧ ...` -/
-- binder_predicate x " ≥ " y:term => `($x ≥ $y)
-- /-- Declare `∃ x < y, ...` as syntax for `∃ x, x < y ∧ ...` -/
-- binder_predicate x " < " y:term => `($x < $y)
-- /-- Declare `∃ x ≤ y, ...` as syntax for `∃ x, x ≤ y ∧ ...` -/
-- binder_predicate x " ≤ " y:term => `($x ≤ $y)
-- /-- Declare `∃ x ≠ y, ...` as syntax for `∃ x, x ≠ y ∧ ...` -/
-- binder_predicate x " ≠ " y:term => `($x ≠ $y)

-- /-- Declare `∀ x ∈ y, ...` as syntax for `∀ x, x ∈ y → ...` and `∃ x ∈ y, ...` as syntax for
-- `∃ x, x ∈ y ∧ ...` -/
-- binder_predicate x " ∈ " y:term => `($x ∈ $y)

-- /-- Declare `∀ x ∉ y, ...` as syntax for `∀ x, x ∉ y → ...` and `∃ x ∉ y, ...` as syntax for
-- `∃ x, x ∉ y ∧ ...` -/
-- binder_predicate x " ∉ " y:term => `($x ∉ $y)

-- @[inherit_doc] scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex
