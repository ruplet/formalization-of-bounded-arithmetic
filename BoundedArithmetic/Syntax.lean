import Mathlib.ModelTheory.Syntax

import BoundedArithmetic.IsEnum

namespace FirstOrder
namespace Language

universe u
variable {L : Language}
variable {α β : Type u} {n : Nat}

namespace BoundedFormula

-- Computable version of: `iSup`
def iSup' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊔ ·) ⊥

-- Computable version of: `iInf`
def iInf' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace Formula

-- Computable version of: `iAlls f φ`
def iAlls' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).alls

-- Computable version of: `iExs f φ`
def iExs' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).exs

-- Computable version of: `iExsUnique f φ`
def iExsUnique' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs' <| φ ⊓ iAlls'
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf' fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

-- Computable version of: iSup
def iSup' [enum : IsEnum α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup' f

-- Computable version of: iInf
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

@[simp]
theorem bdEqual {L : Language} {a b} {n} (g : a ≃ b) {t1 t2 : L.Term (a ⊕ Fin n)}
  : ((t1 =' t2).relabelEquiv g)
    =
    (t1.relabel (Sum.map g id)) =' (t2.relabel (Sum.map g id)) :=
by
  rfl

-- TODO: this was very hard to prove. simp sets of Equiv and of mapTermRel are bad.
theorem comp_inv {L : Language} {α β} {m} {φ : L.BoundedFormula α m} (f : α ≃ β)
  : (relabelEquiv f.symm ((relabelEquiv f) φ)) = φ :=
by
  unfold relabelEquiv mapTermRelEquiv
  dsimp only [Equiv.coe_refl, Equiv.coe_fn_mk]
  rw [mapTermRel_mapTermRel]
  unfold Function.comp
  unfold Equiv.sumCongr
  simp only [Equiv.coe_refl, _root_.Equiv.symm_symm, Equiv.refl_symm, Term.relabelEquiv_apply,
    Equiv.coe_fn_mk, Term.relabel_relabel, Sum.map_comp_map, _root_.Equiv.symm_comp_self,
    Function.comp_id, Sum.map_id_id, Term.relabel_id_eq_id, id_eq]
  apply mapTermRel_id_id_id

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

namespace relabelEquiv

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

@[simp]
theorem ex {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabelEquiv g = (φ.relabelEquiv g).ex := by
  simp only [BoundedFormula.ex, BoundedFormula.not]
  simp only [relabelEquiv.imp, all, imp.injEq, all.injEq, true_and, Bot.bot]
  constructor
  · simp only [relabelEquiv.falsum]
  · simp only [relabelEquiv.falsum]


@[simp]
theorem alls {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α k) :
    φ.alls.relabelEquiv g = (φ.relabelEquiv g).alls := by
  induction k with
  | zero =>
    unfold BoundedFormula.alls
    simp only
  | succ m ih =>
    apply ih


@[simp]
theorem exs {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α k) :
    φ.exs.relabelEquiv g = (φ.relabelEquiv g).exs := by
  induction k with
  | zero =>
    unfold BoundedFormula.exs
    simp only
  | succ m ih =>
    apply ih

@[simp]
theorem iExs' {α β γ} {k} [henum : IsEnum β] (hs : k = henum.size) (g : α ≃ γ) (φ : L.Formula (α ⊕ β)) :
    BoundedFormula.relabelEquiv g (φ.iExs')
    = Formula.iExs' (φ.relabelEquiv (Equiv.sumCongr g (_root_.Equiv.refl β))) :=
by
  unfold Formula.iExs'
  rw [exs]
  congr
  sorry

@[simp]
theorem iAlls' {α β γ} {k} [henum : IsEnum β] (hs : k = henum.size) (g : α ≃ γ) (φ : L.Formula (α ⊕ β)) :
    BoundedFormula.relabelEquiv g (φ.iAlls')
    = Formula.iAlls' (φ.relabelEquiv (Equiv.sumCongr g (_root_.Equiv.refl β))) :=
by
  unfold Formula.iAlls'
  rw [alls]
  congr
  sorry

@[simp]
theorem inf {L : Language} {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊓ (ψ.relabelEquiv g) :=
  rfl


end relabelEquiv

end BoundedFormula
