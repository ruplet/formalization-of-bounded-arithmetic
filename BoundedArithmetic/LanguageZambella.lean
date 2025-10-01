import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Order

import BoundedArithmetic.LanguagePeano

universe u v

namespace FirstOrder
namespace Language

-- Definition 4.4, Draft page 70 (page 81 of pdf)
-- + note about adding the axiom "E" and empty-string constant in a section below
inductive ZambellaFunc : Nat -> Type u
| zero :  ZambellaFunc 0
| one :   ZambellaFunc 0
| empty : ZambellaFunc 0
| len :   ZambellaFunc 1
| add :   ZambellaFunc 2
| mul :   ZambellaFunc 2
deriving DecidableEq

inductive ZambellaRel : Nat -> Type u
-- | eqsort, eqstr -- we will use built-in equality syntax from ModelTheory lib
| isnum : ZambellaRel 1
| isstr : ZambellaRel 1
| leq :   ZambellaRel 2
| mem :   ZambellaRel 2
deriving DecidableEq

def zambella : Language :=
{ Functions := ZambellaFunc,
  Relations := ZambellaRel
}

namespace zambella
variable {a : Type u}

instance : Language.IsOrdered zambella where
  leSymb := ZambellaRel.leq

@[simp] instance : Zero (zambella.Term a) where
  zero := Constants.term .zero

@[simp] instance : One (zambella.Term a) where
  one := Constants.term .one

class HasEmptySet (α : Type*) where
  empty : α

@[simp] instance : HasEmptySet (zambella.Term a) where
  empty := Constants.term .empty

class HasLen (α : Type u) (β : Type v) where
  len : α -> β

@[simp] instance : HasLen (zambella.Term a) (zambella.Term a) where
  len := Functions.apply₁ .len

@[simp] instance : Add (zambella.Term a) where
  add := Functions.apply₂ .add

@[simp] instance : Mul (zambella.Term a) where
  mul := Functions.apply₂ .mul

class HasTypes_is (α : Type*) where
  int : α -> Prop
  str : α -> Prop
  dec   : ∀ x, int x ∨ str x
  excl  : ∀ x, (int x -> ¬str x) ∧ (str x -> ¬int x)


section Semantics

instance {M} [h : zambella.Structure M] : Zero M :=
  ⟨h.funMap ZambellaFunc.zero ![]⟩

instance {M} [h : zambella.Structure M] : One M :=
  ⟨h.funMap ZambellaFunc.one ![]⟩

instance {M} [h : zambella.Structure M] : Add M :=
  ⟨fun x y => h.funMap ZambellaFunc.add ![x, y]⟩

instance {M} [h : zambella.Structure M] : Mul M :=
  ⟨fun x y => h.funMap ZambellaFunc.mul ![x, y]⟩

instance {M} [h : zambella.Structure M] : LE M :=
  ⟨fun x y => h.RelMap ZambellaRel.leq ![x, y]⟩

instance {M} [h : zambella.Structure M] : LT M where
  lt x y := x <= y ∧ x ≠ y

instance {M} [h : zambella.Structure M] : HasEmptySet M :=
  ⟨h.funMap ZambellaFunc.empty ![]⟩

instance {M} [h : zambella.Structure M] : HasLen M M :=
  ⟨fun x => h.funMap ZambellaFunc.len ![x]⟩

instance {M} [h : zambella.Structure M] : Membership M M :=
  ⟨fun x y => h.RelMap ZambellaRel.mem ![x, y]⟩

instance {M} [h : zambella.Structure M] : peano.Structure M where
  funMap := fun {arity} f =>
    match arity, f with
    | 0, PeanoFunc.zero => fun _ => 0
    | 0, PeanoFunc.one => fun _ => 1
    | 2, PeanoFunc.add => fun args => (args 0) + (args 1)
    | 2, PeanoFunc.mul => fun args => (args 0) * (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    | 2, PeanoRel.leq => fun args => (args 0) <= (args 1)

-- use Zero, One instances explicitly to avoid circular dependency
instance {M} [h : zambella.Structure M] (n) : OfNat M n where
  ofNat := aux n
where
  aux : Nat -> M
    | 0 => Zero.zero
    | 1 => One.one
    | n + 1 => (aux n) + One.one

@[simp] lemma realize_zero_to_zero {M} [zambella.Structure M] {a} {env : a → M} :
  Language.Term.realize env (0 : zambella.Term a) = (0 : M) := by
  simp only [OfNat.ofNat, Zero.zero]
  simp only [zambella, Term.realize_constants]
  rfl

-- it is important to define OfNat 1 as 1, not (0+1), as the later needs an axiom to
-- be asserted equal to 1.
@[simp] lemma realize_one_to_one {M} [zambella.Structure M] {a} {env : a → M} :
  Term.realize env (1 : zambella.Term a) = (1 : M) := by
  simp only [OfNat.ofNat, One.one]
  simp only [zambella, Term.realize_constants]
  rfl

@[simp] lemma realize_add_to_add {M} [h : zambella.Structure M] {a} {env : a → M}
    (t u : zambella.Term a) :
  Term.realize env (t + u) = Term.realize env t + Term.realize env u := by
  simp only [zambella, HAdd.hAdd, Add.add]
  -- TODO: why the below doesn't work without @?
  rw [@Term.realize_functions_apply₂]

@[simp] lemma realize_mul_to_mul {M} [zambella.Structure M] {a} {env : a → M}
    (t u : zambella.Term a) :
  Term.realize env (t * u) = Term.realize env t * Term.realize env u := by
  simp only [HMul.hMul, Mul.mul]
  rw [@Term.realize_functions_apply₂]

@[simp] lemma realize_leq_to_leq {M} [h : zambella.Structure M] {a} {env : a → M}
    {k} (t u : zambella.Term (a ⊕ (Fin k))) {xs} :
  (t.le u).Realize env xs = (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  simp only [LE.le, Term.le, Relations.boundedFormula₂]
  rw [← @BoundedFormula.realize_rel₂]
  unfold Relations.boundedFormula₂
  rfl

@[simp] lemma realize_leq_to_leq' {M} [h : zambella.Structure M] {a} {env : a → M}
    {k} (t u : zambella.Term (a ⊕ (Fin k))) {xs} :
  (BoundedFormula.rel ZambellaRel.leq ![t, u]).Realize env xs = (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  simp only [LE.le]
  rw [← @BoundedFormula.realize_rel₂]
  unfold Relations.boundedFormula₂ Relations.boundedFormula
  rfl

@[simp] lemma realize_leq_to_leq'' {M} [h : zambella.Structure M] {a} {env : a → M}
    {k} (t u : zambella.Term (a ⊕ (Fin k))) {xs} :
  h.RelMap ZambellaRel.leq ![t.realize (Sum.elim env xs), u.realize (Sum.elim env xs)] <-> (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  exact Eq.to_iff rfl

end Semantics

/-- The membership relation of two terms as a bounded formula -/
def _root_.FirstOrder.Term.in {a : Type u} {n} (t1 t2 : zambella.Term (a ⊕ (Fin n))) : zambella.BoundedFormula a n :=
  Relations.boundedFormula₂ ZambellaRel.mem t1 t2
@[inherit_doc] scoped[FirstOrder.Language] infixl:88 " ∈' " => Term.in

/-- The not-mem relation of two terms as a bounded formula -/
def _root_.FirstOrder.Term.notin {a : Type u} {n} (t1 t2 : zambella.Term (a ⊕ (Fin n))) : zambella.BoundedFormula a n :=
  ∼(t1 ∈' t2)

@[inherit_doc] scoped[FirstOrder.Language] infixl:88 " ∉' " => Term.notin


end FirstOrder.Language.zambella
