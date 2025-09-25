public import Init.NotationExtra

import Mathlib.ModelTheory.Syntax

import BoundedArithmetic.IsEnum
import BoundedArithmetic.IsEnumProperties

universe u v w u' v'
namespace FirstOrder
namespace Language

variable {L : Language}
variable {α β : Type u} {n : Nat}

namespace BoundedFormula

/-- Computable version of: iSup

Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
@[simp]
def iSup' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊔ ·) ⊥

/-- Computable version of: iInf

Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
@[simp]
def iInf' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace Formula

/-- Computable version of: `iAlls f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by universally
quantifying over all variables `Sum.inr _`.
-/
@[simp]
def iAlls' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).alls

/-- Computable version of: `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
@[simp]
def iExs' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).exs

/-- Computable version of: `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
@[simp]
def iExsUnique' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs' <| φ ⊓ iAlls'
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf' fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))


/-- Computable version of: iSup

Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
@[simp]
def iSup' [enum : IsEnum α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup' f

/-- Computable version of: iInf

Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
@[simp]
def iInf' [enum : IsEnum α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf' f

end Formula


namespace BoundedFormula


namespace relabelEquiv

@[simp]
theorem falsum {α β} (g : α ≃ β) {k} :
    (falsum : L.BoundedFormula α k).relabelEquiv g = falsum :=
  rfl

@[simp]
theorem all {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabelEquiv g = (φ.relabelEquiv g).all := by
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  simp only [Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk]
  conv => lhs; unfold mapTermRel
  simp

-- @[simp]
-- theorem relabelEquiv_ex {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
--     φ.ex.relabelEquiv g = (φ.relabelEquiv g).ex := by
--   rw [relabelEquiv]
--   rw [mapTermRelEquiv]
--   rw [relabelEquiv]
--   rw [mapTermRelEquiv]
--   simp only [Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk]
--   conv => lhs; unfold mapTermRel
--   sorry

@[simp]
theorem imp {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabelEquiv g = (φ.relabelEquiv g).imp (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem nf {α β}(g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊓ (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem sup {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊔ (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem rel {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k} {ts : Fin k -> L.Term (a ⊕ Fin n)}
  : ((BoundedFormula.rel R ts).relabelEquiv g : L.BoundedFormula b n) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n))) : L.BoundedFormula b n) :=
by
  rfl

@[simp]
theorem eq {L : Language} {a b} {n} (g : a ≃ b) {t1 t2 : L.Term (a ⊕ Fin n)}
  : ((t1 =' t2).relabelEquiv g : L.BoundedFormula b n)
    =
      (
        (  t1.relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n)
        =' t2.relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n)
        ) : L.BoundedFormula b n
      ) :=
by
  rfl

end relabelEquiv

namespace relabel

@[simp]
theorem sup {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabel g = (φ.relabel g) ⊔ (ψ.relabel g) :=
  rfl

@[simp]
theorem inf {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabel g = (φ.relabel g) ⊓ (ψ.relabel g) :=
  rfl

end relabel

end BoundedFormula
