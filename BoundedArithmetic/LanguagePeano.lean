import Mathlib.ModelTheory.Order

universe u v

namespace FirstOrder
namespace Language

-- this style of definition is inspired by https://github.com/leanprover-community/mathlib4/blob/2cb771d3006e8b7579f66990fed1b433bf2e7fed/Mathlib/ModelTheory/Arithmetic/Presburger/Basic.lean
-- Definition 2.3, page 12 of draft (23 of pdf);
--   + remark in section 3.1, top of page 34 of draft (45 of pdf)
-- note: the equality relation is present by default in Mathlib.ModelTheory
-- it is explicit in Cook and Nguyen, but it doesn't seem to lead to any inconsistencies
-- note: checking if 'x = y is not always trivial; if x and y are long bit-strings,
-- encoded as lists (e.g. 3 encoded as S(S(S(Z)))), checking for their equality
-- is linear-time, thus not trivial at all. But here we only use equality in proofs
-- and the only way to assert equality is to prove it from axioms. So it seems like we'll
-- never run into the problem of having to brute-force checking for equality
inductive PeanoFunc : Nat -> Type*
  | zero : PeanoFunc 0
  | one : PeanoFunc 0
  | add : PeanoFunc 2
  | mul : PeanoFunc 2
  deriving DecidableEq

inductive PeanoRel : Nat -> Type*
  | leq : PeanoRel 2
  deriving DecidableEq

def peano : Language :=
{ Functions := PeanoFunc,
  Relations := PeanoRel
}

namespace peano
variable {a : Type u}

instance : Language.IsOrdered peano where
  leSymb := PeanoRel.leq

@[simp] instance : Zero (peano.Term a) where
  zero := Constants.term .zero

@[simp] instance : One (peano.Term a) where
  one := Constants.term .one

@[simp] instance : Add (peano.Term a) where
  add := Functions.apply₂ .add

@[simp] instance : Mul (peano.Term a) where
  mul := Functions.apply₂ .mul


-- @[simp] instance : SMul ℕ (peano.Term a) where
--   smul := nsmulRec
-- @[simp] theorem zero_nsmul {t : peano.Term a} : 0 • t = 0 := rfl
-- @[simp] theorem succ_nsmul {t : peano.Term a} {n : ℕ} : (n + 1) • t = n • t + t := rfl

-- instance : NatCast (peano.Term a) where
--   natCast := Nat.unaryCast

-- inspired by https://github.com/leanprover-community/mathlib4/blob/cff2a6ea669abe2e384ea4c359f20ee90a5dc855/Mathlib/ModelTheory/Syntax.lean#L732
-- standard precedence of ≤, ≠, <: 50
-- standard precedence of +: 65; of *: 70
-- precedence of ⟹ in ModelTheory: 62, of =': 88
-- the higher precedence the tighter bounding
@[inherit_doc] scoped[FirstOrder.Language] infixl:89 " <=' " => Term.le
@[inherit_doc] scoped[FirstOrder.Language] infixl:89 " <' " => Term.lt

/-- The not-equal relation of two terms as a bounded formula -/
def _root_.FirstOrder.Term.neq {a : Type u} {n} {L : Language} (t1 t2 : L.Term (a ⊕ (Fin n))) : L.BoundedFormula a n :=
  ∼(t1 =' t2)
@[inherit_doc] scoped[FirstOrder.Language] infixl:88 " ≠' " => Term.neq


section Semantics

instance {M} [h : Language.peano.Structure M] : Zero M :=
  ⟨h.funMap PeanoFunc.zero ![]⟩

instance {M} [h : Language.peano.Structure M] : One M :=
  ⟨h.funMap PeanoFunc.one ![]⟩

instance {M} [h : Language.peano.Structure M] : Add M :=
  ⟨fun x y => h.funMap PeanoFunc.add ![x, y]⟩

instance {M} [h : Language.peano.Structure M] : Mul M :=
  ⟨fun x y => h.funMap PeanoFunc.mul ![x, y]⟩

instance {M} [h : Language.peano.Structure M] : LE M :=
  ⟨fun x y => h.RelMap PeanoRel.leq ![x, y]⟩

def natToM {M} [h : Language.peano.Structure M] : Nat -> M
| 0 => 0
| 1 => 1
| n + 1 => natToM n + 1

instance {M} [h : Language.peano.Structure M] (n) : OfNat M n where
  ofNat := natToM n

@[simp] lemma realize_zero_to_zero {M} [Language.peano.Structure M] {a} {env : a → M} :
  Language.Term.realize env (0 : Language.peano.Term a) = (0 : M) := by
  simp only [OfNat.ofNat, Zero.zero]
  simp only [peano, Term.realize_constants, natToM, OfNat.ofNat, Zero.zero]
  rfl

-- it is important to define OfNat 1 as 1, not (0+1), as the later needs an axiom to
-- be asserted equal to 1.
@[simp] lemma realize_one_to_one {M} [peano.Structure M] {a} {env : a → M} :
  Term.realize env (1 : peano.Term a) = (1 : M) := by
  simp only [OfNat.ofNat, One.one]
  simp only [peano, Term.realize_constants, natToM, OfNat.ofNat]
  rfl

@[simp] lemma realize_add_to_add {M} [h : peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t + u) = Term.realize env t + Term.realize env u := by
  simp only [peano, HAdd.hAdd, Add.add]
  -- TODO: why the below doesn't work without @?
  rw [@Term.realize_functions_apply₂]

@[simp] lemma realize_mul_to_mul {M} [peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t * u) = Term.realize env t * Term.realize env u := by
  simp only [HMul.hMul, Mul.mul]
  rw [@Term.realize_functions_apply₂]

@[simp] lemma realize_leq_to_leq {M} [h : peano.Structure M] {a} {env : a → M}
    {k} (t u : peano.Term (a ⊕ (Fin k))) {xs} :
  (t.le u).Realize env xs = (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  simp only [LE.le, Term.le, Relations.boundedFormula₂]
  rw [← @BoundedFormula.realize_rel₂]
  unfold Relations.boundedFormula₂
  rfl

@[simp] lemma realize_leq_to_leq' {M} [h : peano.Structure M] {a} {env : a → M}
    {k} (t u : peano.Term (a ⊕ (Fin k))) {xs} :
  (BoundedFormula.rel PeanoRel.leq ![t, u]).Realize env xs = (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  simp only [LE.le]
  rw [← @BoundedFormula.realize_rel₂]
  unfold Relations.boundedFormula₂ Relations.boundedFormula
  rfl

@[simp] lemma realize_leq_to_leq'' {M} [h : peano.Structure M] {a} {env : a → M}
    {k} (t u : peano.Term (a ⊕ (Fin k))) {xs} :
  h.RelMap PeanoRel.leq ![t.realize (Sum.elim env xs), u.realize (Sum.elim env xs)] <-> (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  exact Eq.to_iff rfl

end Semantics
end FirstOrder.Language.peano
