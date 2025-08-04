-- https://github.com/leanprover-community/mathlib4/blob/0c55a410bbb4c0f54eb649c14f25d4a89bb2a49e/Mathlib/ModelTheory/Syntax.lean
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import V0Theory.TwoSortedModelTheory.Basic
-- import V0Theory.TwoSortedModelTheory.LanguageMap
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Logic.Nonempty
import Mathlib.Data.Multiset.Basic


namespace TwoSortedFirstOrder

universe w u' v'

namespace Language

universe u v x
variable (Sorts: Type x) [Fintype Sorts]
variable (L : Language.{u, v} Sorts) -- {L' : Language Sorts}
variable (varIndT: Type u') (varIndT': Type v')

open TwoSortedFirstOrder

-- open Structure
open Fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term : (sort: Sorts) -> Type max u u' x
  | var sort : varIndT -> Term sort
  | func sort :
    {arities : Sorts -> Nat} ->
    ∀
    (_f : L.Functions arities sort)
    (_ts : (s : Sorts) → ((Fin (arities s)) → Term s)),
    Term sort

-- export Term (var func)

namespace Term
-- @[simp]
def relabel {s: Sorts} (g : varIndT → varIndT') : L.Term Sorts varIndT s → L.Term Sorts varIndT' s
  | @var Sorts L varIndT s i => var s (g i)
  | @func Sorts L _ s _ f ts => func s f fun {s' i} => (ts s' i).relabel g

end Term

-- variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}
-- variable {a : Type u'}
-- variable {L}

-- variable (L) (α)

-- definition II.2.2 CookNguyen
/-- `OpenFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
  -- - Formulas use a modified version of de Bruijn variables. Specifically, a `L.BoundedFormula α n`
  -- is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
  -- indexed by `Fin n`, which can. For any `φ : L.BoundedFormula α (n + 1)`, we define the formula
  -- `∀' φ : L.BoundedFormula α n` by universally quantifying over the variable indexed by
  -- `n : Fin (n + 1)`.
  -- https://github.com/flypitch/flypitch/blob/d72904c17fbb874f01ffe168667ba12663a7b853/src/fol.lean#L502
inductive OpenFormula : Type max u v u' x
  | falsum : OpenFormula
  | rel
    {arities : Sorts -> Nat}
    (R : L.Relations arities)
    (ts :
      (s : Sorts) -> ((Fin (arities s)) → L.Term Sorts (varIndT) s)
    )
    : OpenFormula
  | imp (f1 f2 : OpenFormula) : OpenFormula
-- | rel
--   {n}
--   {arities : Sorts -> Nat}
--   (R : L.Relations arities)
--   (ts :
--     (s : Sorts) -> ((Fin (arities s)) → L.Term Sorts (varIndT ⊕ (Fin n)) s)
--   )
--   : OpenFormula n
-- | not {n} (A : OpenFormula n) : OpenFormula n
-- | and {n} (A B : OpenFormula n) : OpenFormula n
-- | or {n} (A B : OpenFormula n) : OpenFormula n
-- | truth {n} : OpenFormula n
-- | all {n} (f : OpenFormula (n + 1)) : OpenFormula n
-- implication A -> B is defined as not A or B (classical logic!)
-- | ex {n} (f : OpenFormula (n + 1)) : OpenFormula n

inductive Formula : Type max u v u' x
| openf (A : OpenFormula Sorts L varIndT) : Formula
| all (A : OpenFormula Sorts L varIndT) : Formula

def notf {Sorts : Type x} {L : Language Sorts} {varIndT : Type u'} (A : OpenFormula Sorts L varIndT)
  : OpenFormula Sorts L varIndT :=
  OpenFormula.imp A OpenFormula.falsum

def andf {Sorts} {varIndT} {L : Language Sorts} (A B : OpenFormula Sorts L varIndT)
  : OpenFormula Sorts L varIndT :=
  notf (OpenFormula.imp A (notf B))

def orf {Sorts : Type x} {L : Language Sorts} (A B : OpenFormula Sorts L varIndT)
  : OpenFormula Sorts L varIndT :=
  OpenFormula.imp (notf A) B


-- open Set

-- there should be a type Theory
-- variable (L)
-- @[reducible] def Theory := set $ sentence L
-- variable {L}

-- should Theory be set, multiset, list, finset, fintype, set finite?
-- def Theory :=
abbrev Theory := Multiset (OpenFormula Sorts L varIndT)

-- Natural deduction: https://github.com/flypitch/flypitch/blob/master/src/fol.lean
inductive prf : (Theory Sorts L varIndT) -> (OpenFormula Sorts L varIndT) -> Type max u v u' x
| axm     {Γ} {A} (h : A ∈ Γ) : prf Γ A
| impI    {Γ} {A B} (h : prf (insert A Γ) B) : prf Γ (OpenFormula.imp A B)
| impE    {Γ} (A) {B} (h₁ : prf Γ (OpenFormula.imp A B)) (h₂ : prf Γ A) : prf Γ B
| falsumE {Γ} {A} (h : prf (insert (notf A) Γ) (OpenFormula.falsum)) : prf Γ A
-- | allI    {Γ A} (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
-- | allE₂   {Γ} A t (h : prf Γ (∀' A)) : prf Γ (A[t // 0])
-- | ref     (Γ t) : prf Γ (t ≃ t)
-- | subst₂  {Γ} (s t f) (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f[s // 0])) : prf Γ (f[t // 0])
-- | axm {Gamma} {goal} (h: goal ∈ Gamma) : Proof Gamma goal
-- | impI {Gamma} {A} {B} (h: Proof (insert A Gamma) B) : Proof Gamma (OpenFormula.imp A B)
-- | impE {Gamma}

def provable (T : Multiset (OpenFormula Sorts L varIndT)) (f : OpenFormula Sorts L varIndT) := Inhabited (prf Sorts L varIndT T f)

-- set_option diagnostics true

def axm1 (Gamma : Multiset (OpenFormula Sorts L varIndT)) (f : OpenFormula Sorts L varIndT)
  : provable Sorts L varIndT (insert f Gamma) f :=
  by
    constructor
    apply prf.axm
    simp

def axm2 (Gamma : Multiset (OpenFormula Sorts L varIndT)) (A B : OpenFormula Sorts L varIndT)
  : provable Sorts L varIndT (insert A (insert B Gamma)) B :=
  by
    constructor
    apply prf.axm
    simp

def weakening {Gamma} {Delta} {f : OpenFormula Sorts L varIndT} (H1: Gamma ⊆ Delta) (H2 : provable Sorts L varIndT Gamma f)
  : provable Sorts L varIndT Delta f :=
  by
    sorry
    -- constructor
    -- induction H2.default
    -- match H2.default with
    -- | prf.axm h =>
    --   apply prf.axm
    --   apply H1 h
    -- | prf.impI h =>
    --   apply prf.impI
    -- | prf.impE h h1 h2 =>
    --   sorry
    -- | prf.falsumE falsumE =>
    --   sorry

def weakening1 {Gamma} {f1 f2 : OpenFormula Sorts L varIndT} (H : provable Sorts L varIndT Gamma f2)
  : prf Sorts L varIndT (insert f1 Gamma) f2 :=
  sorry
  -- weakening Sorts L varIndT (Multiset.subset_cons Gamma f1) H

def andI {Gamma} {f1 f2 : OpenFormula Sorts L varIndT} (H1: provable Sorts L varIndT Gamma f1) (H2: provable Sorts L varIndT Gamma f2)
  : provable Sorts L varIndT Gamma (andf f1 f2) :=
  by
    unfold andf
    unfold notf
    constructor
    apply prf.impI
    apply prf.impE f2
    {
      apply prf.impE f1
      apply prf.axm
      aesop
      apply weakening1 Sorts L varIndT H1
    }
    sorry

def andE1 {Gamma} {f1 f2 : OpenFormula Sorts L varIndT} (H1: provable Sorts L varIndT Gamma (andf f1 f2))
  : provable Sorts L varIndT Gamma f1 := sorry

def andE2 {Gamma} {f1 f2 : OpenFormula Sorts L varIndT} (H1: provable Sorts L varIndT Gamma (andf f1 f2))
  : provable Sorts L varIndT Gamma f2 := sorry

-- open OpenFormula
-- def deduction {Gamma} {A B : OpenFormula Sorts L varIndT} (H : provable Gamma (imp A B)) : provable (insert A Gamma) B :=


end Language
end TwoSortedFirstOrder
