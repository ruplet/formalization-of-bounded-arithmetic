-- https://github.com/leanprover-community/mathlib4/blob/0c55a410bbb4c0f54eb649c14f25d4a89bb2a49e/Mathlib/ModelTheory/Basic.lean
-- import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Common
-- import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Fintype.Basic

namespace TwoSortedFirstOrder
universe u v x -- u' v' w w'

-- variable (sorta sortb : Type)

-- inductive Sorts where
-- | sorta
-- | sortb

variable (Sorts : Type x) [Fintype Sorts]

-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  /-- For every arity, a `Type*` of functions of that arity -/
  Functions : (Sorts -> Nat) -> Sorts -> Type u
  /-- For every arity, a `Type*` of relations of that arity -/
  Relations : (Sorts -> Nat) -> Type v

-- instance instDecidableEqFunctions {f : (Sorts -> Nat) -> Sorts -> Type u}

namespace Language

universe w
variable (L : Language Sorts)
variable (M : Sorts -> Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
-- @[ext]
class Structure where
  /-- Interpretation of the function symbols -/
  funMap sort : ∀ {arities}, L.Functions arities sort → ((s : Sorts) -> (Fin (arities s)) → M s) → (M sort)
  /-- Interpretation of the relation symbols -/
  relMap : ∀ {arities}, L.Relations arities → ((s : Sorts) -> (Fin (arities s)) → M s) → Prop

end Language
end TwoSortedFirstOrder
