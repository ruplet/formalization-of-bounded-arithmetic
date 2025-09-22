-- for a quick demo, jump straight to `theorem add_assoc`
import Lean
import BoundedArithmetic.BoundedModelTheory.Basic
import BoundedArithmetic.BoundedModelTheory.Syntax
import BoundedArithmetic.BoundedModelTheory.Complexity
import BoundedArithmetic.BoundedModelTheory.Semantics

open Lean Elab Term Meta Syntax

universe u v

namespace FirstOrder

-- this style of definition is inspired by https://github.com/leanprover-community/mathlib4/blob/2cb771d3006e8b7579f66990fed1b433bf2e7fed/Mathlib/ModelTheory/Arithmetic/Presburger/Basic.lean
-- Definition 2.3, page 12 of draft (23 of pdf);
--   + remark in section 3.1, top of page 34 of draft (45 of pdf)
-- note: the equality relation is present by default in Mathlib.ModelTheory
-- it is explicit in Cook and Nguyen, but it doesn't seem to lead to any inconsistencies
-- note: checking if 'x = y' is not always trivial; if x and y are long bit-strings,
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

def Language.peano : Language :=
{ Functions := PeanoFunc,
  Relations := PeanoRel
}

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

namespace Language

namespace BoundedFormula

@[simp] def boundedEx {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
  -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
  -- `&(Fin.last n)` lifts `n` into Term.var; this denotes just `x`
  -- `t.relabel...` lifts `t` from lv `n` to lv `n + 1`
  ((BoundedFormula.rel PeanoRel.leq ![
    (&(Fin.last n)),
    (t.relabel $ Sum.map id (Fin.succEmb n))
    ]
  ) ⊓ f).ex


@[simp] def boundedAll {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
  ((BoundedFormula.rel PeanoRel.leq ![
    (&(Fin.last n)),
    (t.relabel $ Sum.map id (Fin.succEmb n))
    ]
  ) ⟹ f).all

-- @[simp] def boundedExUnique {a} {n} (t : peano.Term (a ⊕ (Fin n))) (f : peano.BoundedFormula a (n + 1)) : peano.BoundedFormula a n :=
--   -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
--   -- `&(Fin.last n)` lifts `n` into Term.var; this denotes just `x`
--   -- `t.relabel...` lifts `t` from lv `n` to lv `n + 1`
--   ((BoundedFormula.rel PeanoRel.leq ![
--     (&(Fin.last n)),
--     (t.relabel $ Sum.map id (Fin.succEmb n))
--     ]
--   ) ⊓ f ⊓ (forall y, y<=t -> phi(y) -> y = x0 )).ex

inductive DisplayedFV1 | x deriving DecidableEq
inductive DisplayedFV2 | x | y deriving DecidableEq
inductive DisplayedFV3 | x | y | z deriving DecidableEq


@[simp] def Empty.equivFin0 : Empty ≃ Fin 0 where
  toFun fv := nomatch fv
  invFun n := nomatch n
  left_inv := by intro fv; cases fv
  right_inv := by intro n; nomatch n

@[simp] def DisplayedFV1.equivFin1 : DisplayedFV1 ≃ Fin 1 where
  toFun fv := match fv with | .x => 0
  invFun n := match n with | ⟨0, _⟩ => .x
  left_inv := by intro fv; cases fv; · simp
  right_inv := by intro n; match n with | ⟨0, _⟩ => simp

@[simp] def DisplayedFV2.equivFin2 : DisplayedFV2 ≃ Fin 2 where
  toFun fv := match fv with | .x => 0 | .y => 1
  invFun n := match n with | ⟨0, _⟩ => .x | ⟨1, _⟩ => .y
  left_inv := by (
    intro fv
    cases fv
    · simp
    · simp
  )
  right_inv := by (
    intro n
    match n with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp
  )

@[simp] def DisplayedFV3.equivFin3 : DisplayedFV3 ≃ Fin 3 where
  toFun fv := match fv with | .x => 0 | .y => 1 | .z => 2
  invFun n := match n with | ⟨0, _⟩ => .x | ⟨1, _⟩ => .y | ⟨2, _⟩ => .z
  left_inv := by (
    intro fv
    cases fv
    · simp
    · simp
    · simp
  )
  right_inv := by (
    intro n
    match n with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp
    | ⟨2, _⟩ => simp
  )

/- Notes about de Bruijn indices as used in Mathlib.ModelTheory
  Take a look at how is BoundedFormula.Realize implemented:
  `| _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)`

  Recall that  `Fin.snoc xs x` takes a tuple `xs : Fin n -> SomeType` and turns
  it into a tuple with `x` appended at the end,
  i.e. `xs' : Fin (n + 1) -> SomeType` with `n` mapped into `x`

  Now, how is BoundedFormula.relabel implemented?
  Not the way we want - we can only substitute a free var with a specific term,
  but the term has to be different, depending on the quantifier depth of
  the place where the free var occurs in the ofrmua

  One attempt:: Mathlib.ModelTheory offers us constantsVarsEquiv function!
  e.g. to move free vars into language constants: constantsVarsEquiv.symm phi.alls

  Second attempt: use iAlls and special free var types carefully!
--/

@[simp] def x {k} : peano.Term (DisplayedFV1 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV1.x)
@[simp] def x' {k} : peano.Term (DisplayedFV2 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV2.x)
@[simp] def y' {k} : peano.Term (DisplayedFV2 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV2.y)
@[simp] def x'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.x)
@[simp] def y'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.y)
@[simp] def z'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.z)

-- IMPORTANT: this has to be done using relabelEquiv
-- so we know by design that the relabel is a bijection!
@[simp]
def display_x (phi : peano.Formula DisplayedFV1) : peano.Formula (DisplayedFV1 ⊕ Empty) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .x => Sum.inl .x
    ),
    invFun := (fun fv => match fv with | .inl _ => .x)
    right_inv := by
      refine Function.rightInverse_of_injective_of_leftInverse ?_ (congrFun rfl)
      intro a b _
      cases a with
      | inl a' =>
        cases b with
        | inl b' => simp
        | inr b' => apply Empty.elim b'
      | inr a' => apply Empty.elim a'
  }


@[simp]
def display_x' {n} (phi : peano.BoundedFormula DisplayedFV2 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV1) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inl .x
  | .y => Sum.inr .x
  )) : DisplayedFV2 -> ((DisplayedFV1 ⊕ DisplayedFV1) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

-- TODO: odwrocilem tutaj kolejnosc inl, inr. reszta teraz jest niekonsekwentnie
@[simp]
def display_y' {n} (phi : peano.BoundedFormula DisplayedFV2 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV1) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inl .x
  | .y => Sum.inr .x
  )) : DisplayedFV2 -> ((DisplayedFV1 ⊕ DisplayedFV1) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
def display_x'' {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV2) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inl .x
  | .y => Sum.inr .x
  | .z => Sum.inr .y
  )) : DisplayedFV3 -> ((DisplayedFV1 ⊕ DisplayedFV2) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
def display_y'' {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV2) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inr .x
  | .y => Sum.inl .x
  | .z => Sum.inr .y
  )) : DisplayedFV3 -> ((DisplayedFV1 ⊕ DisplayedFV2) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
def display_z'' {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV2) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inr .x
  | .y => Sum.inr .y
  | .z => Sum.inl .x
  )) : DisplayedFV3 -> ((DisplayedFV1 ⊕ DisplayedFV2) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

end BoundedFormula

namespace Formula

/-- Computable version of FirstOrder.Language.Formula.iAlls -/
@[simp] def iAllsComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

@[simp] def iAllsComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  (BoundedFormula.relabel (fun a => Sum.inr $ e a) φ).alls

@[simp] def iExsComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

@[simp] def iExsComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  (BoundedFormula.relabel (fun a => Sum.inr $ e a) φ).exs

@[simp] def Fintype.ofFiniteComputable (α : Type*) {k} (e : α ≃ Fin k) : Fintype α := by
  apply @Fintype.ofBijective (Fin k) α _ e.invFun
  rw [Equiv.invFun_as_coe]
  exact _root_.Equiv.bijective e.symm

@[simp] def Finset.toListComputable {α} {k} (e : α ≃ Fin k) : List α :=
  List.ofFn e.symm

@[simp] def iInfComputable {L : Language} {α β} {n k} (e : β ≃ Fin k) (f : β -> L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ : Fintype β := Fintype.ofFiniteComputable β e
  ((Finset.toListComputable e).map f).foldr (· ⊓ ·) ⊤

@[simp] def iExsUniqueComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExsComputable e <| φ ⊓ iAllsComputable e
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInfComputable e fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

@[simp] def iExsUniqueComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  iExsComputableEmpty e <| φ ⊓ iAllsComputable e
    ((φ.relabel (fun a => .inr a)).imp <|
      .iInfComputable e fun g => Term.equal (var (.inr g)) (var (.inl g)))

@[simp] def iBdExComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
  iExsComputable BoundedFormula.DisplayedFV1.equivFin1 (
    BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
    ⊓ φ
  )

@[simp] def iBdExUniqueComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
  iExsUniqueComputable BoundedFormula.DisplayedFV1.equivFin1 (
    BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
    ⊓ φ
  )

-- THIS IS FULL GENERALITY!
-- Supports: ∃x ≤ t1() ∧ ∃y ≤ t2(x) ∧ ∃z ≤ t3(x, y) ∧ ... φ(x,y,z,⋯)
-- @[simp] def iBdExsComputableAux {α} : {k : Nat} -> (bdTerms : (i : Fin k) -> peano.Term ((α ⊕ Fin i) ⊕ Fin 0)) -> (φ : peano.Formula (α ⊕ Fin k)) -> peano.Formula α
-- | 0, _, φ => sorry
-- | k + 1, bdTerms, φ => sorry

@[simp] def iBdAllComputable {α} (bdTerm : peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ BoundedFormula.DisplayedFV1)) : peano.Formula α :=
  iAllsComputable BoundedFormula.DisplayedFV1.equivFin1 (
    BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr (BoundedFormula.DisplayedFV1.x))), bdTerm.relabel (Sum.map .inl id)]
    ⟹ φ
  )

end Formula

namespace peano

variable (a : Type u)

@[simp] instance : Zero (peano.Term a) where
  zero := Constants.term .zero

@[simp] instance : One (peano.Term a) where
  one := Constants.term .one

@[simp] instance : Add (peano.Term a) where
  add := Functions.apply₂ .add

@[simp] instance : Mul (peano.Term a) where
  mul := Functions.apply₂ .mul

@[simp] instance : SMul ℕ (peano.Term a) where
  smul := nsmulRec
@[simp] theorem zero_nsmul {t : peano.Term a} : 0 • t = 0 := rfl
@[simp] theorem succ_nsmul {t : peano.Term a} {n : ℕ} : (n + 1) • t = n • t + t := rfl

-- enable converting Nat to objects of Peano
instance : NatCast (peano.Term a) where
  natCast := Nat.unaryCast
-- @[simp, norm_cast] theorem natCast_zero : (0 : ℕ) = (0 : peano.Term a) := rfl
-- @[simp, norm_cast] theorem natCast_succ (n : ℕ) : (n + 1 : ℕ) = (n : peano.Term a) + 1 := rfl
-- @[simp, norm_cast] theorem natCast_add_assoc (n : ℕ) : (n + 1 : ℕ) = (n : peano.Term a) + 1 := rfl

-- inspired by https://github.com/leanprover-community/mathlib4/blob/cff2a6ea669abe2e384ea4c359f20ee90a5dc855/Mathlib/ModelTheory/Syntax.lean#L344
/-- The inequality of two terms as a bounded formula -/
@[simp] def Term.bdNeq {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  ∼(t1 =' t2)

/-- The less-than-or-equal relation of two terms as a bounded formula -/
@[simp] def Term.bdLeq {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  Relations.boundedFormula₂ FirstOrder.PeanoRel.leq t1 t2

-- inspired by https://github.com/leanprover-community/mathlib4/blob/cff2a6ea669abe2e384ea4c359f20ee90a5dc855/Mathlib/ModelTheory/Syntax.lean#L732
-- standard precedence of ≤, ≠, <: 50
-- standard precedence of +: 65; of *: 70
-- precedence of ⟹ in ModelTheory: 62, of =': 88
-- the higher precedence the tighter bounding
@[inherit_doc] scoped[FirstOrder] infixl:88 " ≠' " => Language.peano.Term.bdNeq
@[inherit_doc] scoped[FirstOrder] infixl:89 " <=' " => Language.peano.Term.bdLeq

/-- The less-than relation of two terms as a bounded formula -/
def Term.bdLt {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  (t1 <=' t2) ⊓ ∼(t1 =' t2)

@[inherit_doc] scoped[FirstOrder] infixl:89 " <' " => Language.peano.Term.bdLt


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
  (t <=' u).Realize env xs = (t.realize (Sum.elim env xs) <= u.realize (Sum.elim env xs)) := by
  simp only [LE.le, Term.bdLeq, Relations.boundedFormula₂]
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

end peano

namespace BoundedFormula

-- Definition 3.7, page 36 of draft (47 of pdf)
abbrev isOpen {a} {n} (formula : peano.BoundedFormula a n) := FirstOrder.Language.BoundedFormula.IsQF formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
inductive IsDelta0 {a : Type u} : {n : Nat} -> peano.BoundedFormula a n -> Prop
| of_isQF {phi} (h : BoundedFormula.IsQF phi) : IsDelta0 phi
| imp {phi1 phi2} (h1 : IsDelta0 phi1) (h2 : IsDelta0 phi2) : IsDelta0 (phi1.imp phi2)
| bdEx
  (phi : peano.Formula (a ⊕ DisplayedFV1))
  (t : peano.Term (a ⊕ Fin 0))
  : IsDelta0 $ Formula.iBdExComputable t phi

| bdAll
  (phi : peano.Formula (a ⊕ DisplayedFV1))
  (t : peano.Term (a ⊕ Fin 0))
  : IsDelta0 $ Formula.iBdAllComputable t phi


theorem IsDelta0.imp.mpr {a} {n} (phi psi : peano.BoundedFormula a n) : (IsDelta0 phi ∧ IsDelta0 psi) <-> IsDelta0 (phi.imp psi) := by
  apply Iff.intro
  · intro h
    apply IsDelta0.imp
    · exact h.left
    · exact h.right
  · intro h
    cases h with
    | of_isQF h' =>
      cases h' with
      | of_isAtomic h'' =>
        cases h''
      | imp hPhi hPsi =>
        apply And.intro
        · apply IsDelta0.of_isQF; exact hPhi
        · apply IsDelta0.of_isQF; exact hPsi
    | imp hPhi hPsi =>
      apply And.intro
      · exact hPhi
      · exact hPsi

theorem IsDelta0.not {a} {n} (phi : peano.BoundedFormula a n) : IsDelta0 phi <-> IsDelta0 phi.not := by
  apply Iff.intro
  · intro h
    unfold BoundedFormula.not
    apply IsDelta0.imp
    · exact h
    · constructor
      constructor
  · unfold BoundedFormula.not
    rw [<- IsDelta0.imp.mpr]
    intro h
    exact h.left

theorem IsDelta0.min {a} {n} (phi psi : peano.BoundedFormula a n) : (IsDelta0 phi ∧ IsDelta0 psi) <-> IsDelta0 (phi ⊓ psi) := by
  unfold Min.min instMin
  simp only
  rw [<- IsDelta0.not]
  rw [<- IsDelta0.imp.mpr]
  rw [<- IsDelta0.not]

theorem IsDelta0.max {a} {n} (phi psi : peano.BoundedFormula a n) : (IsDelta0 phi ∧ IsDelta0 psi) <-> IsDelta0 (phi ⊔ psi) := by
  unfold Max.max instMax
  simp only
  rw [<- IsDelta0.imp.mpr]
  rw [<- IsDelta0.not]

theorem IsDelta0.foldr_inf {α} {n} (l : List (peano.BoundedFormula α n)) :
  (l.foldr (· ⊓ ·) ⊤).IsDelta0 ↔ ∀ φ ∈ l, φ.IsDelta0 := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    constructor; apply BoundedFormula.IsQF.top
  | cons φ l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    unfold Min.min instMin
    simp only
    rw [<- IsDelta0.not]
    rw [<- IsDelta0.imp.mpr]
    apply Iff.intro
    · intro h
      apply And.intro
      · exact h.left
      · apply ih.mp
        rw [<- IsDelta0.not] at h
        exact h.right
    · intro h
      apply And.intro
      · exact h.left
      · rw [<- IsDelta0.not]
        apply ih.mpr
        apply h.right

theorem IsDelta0.iInfComputable {α β} {n k} (e : β ≃ Fin k) (f : β -> peano.BoundedFormula α n) :
  (Formula.iInfComputable e f).IsDelta0 ↔ ∀ b, (f b).IsDelta0 := by
  unfold Formula.iInfComputable
  rw [IsDelta0.foldr_inf]
  simp
  rw [Equiv.forall_congr_left e]

-- theorem IsDelta0.iExsComputable {α β} {n k} (e : β ≃ Fin k) (φ: peano.Formula (α ⊕ β)) :
--   (Formula.iExsComputable e φ).IsDelta0 ↔ ∀ b, (f b).IsDelta0 := by
--   unfold Formula.iInfComputable
--   rw [IsDelta0.foldr_inf]
--   simp
--   rw [Equiv.forall_congr_left e]

theorem IsDelta0.iBdExComputable {a} {bdTerm} {phi}
  : IsDelta0 $ (Formula.iBdExComputable bdTerm phi : peano.BoundedFormula a 0) := by
  unfold Formula.iBdExComputable
  unfold Formula.iExsComputable
  unfold BoundedFormula.exs
  unfold BoundedFormula.exs
  apply IsDelta0.bdEx

end BoundedFormula

open BoundedFormula

@[simp] def iAllsFv0 (phi: peano.Formula Empty) := phi.iAllsComputableEmpty Empty.equivFin0
@[simp] def iAllsFv1 (phi: peano.Formula DisplayedFV1) := phi.iAllsComputableEmpty DisplayedFV1.equivFin1
@[simp] def iAllsFv2 (phi: peano.Formula DisplayedFV2) := phi.iAllsComputableEmpty DisplayedFV2.equivFin2
@[simp] def iAllsFv3 (phi: peano.Formula DisplayedFV3) := phi.iAllsComputableEmpty DisplayedFV3.equivFin3

-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
@[simp] def B1_ax : peano.Formula DisplayedFV1 := (x + 1) ≠' 0
@[simp] def B2_ax : peano.Formula DisplayedFV2 := (x' + 1) =' (y' + 1) ⟹ x' =' y'
@[simp] def B3_ax : peano.Formula DisplayedFV1 := (x + 0) =' x
@[simp] def B4_ax : peano.Formula DisplayedFV2 := (x' + (y' + 1)) =' ((x' + y') + 1)
@[simp] def B5_ax : peano.Formula DisplayedFV1 := (x * 0) =' 0
@[simp] def B6_ax : peano.Formula DisplayedFV2 := (x' * (y' + 1)) =' ((x' * y') + x')
@[simp] def B7_ax : peano.Formula DisplayedFV2 := (x' <=' y' ⊓ y' <=' x') ⟹ x' =' y'
@[simp] def B8_ax : peano.Formula DisplayedFV2 := x' <=' (x' + y')
@[simp] def C_ax : peano.Formula Empty := (0 + 1) =' 1

structure BASICModel where
  num : Type*
  -- hInhabited : Inhabited num
  hPeano : peano.Structure num
  B1 : num ⊨ iAllsFv1 B1_ax
  B2 : num ⊨ iAllsFv2 B2_ax
  B3 : num ⊨ iAllsFv1 B3_ax
  B4 : num ⊨ iAllsFv2 B4_ax
  B5 : num ⊨ iAllsFv1 B5_ax
  B6 : num ⊨ iAllsFv2 B6_ax
  B7 : num ⊨ iAllsFv2 B7_ax
  B8 : num ⊨ iAllsFv2 B8_ax
  C  : num ⊨ iAllsFv0 C_ax

instance (M : BASICModel) : peano.Structure M.num where
  funMap := M.hPeano.funMap
  RelMap := M.hPeano.RelMap

@[simp] lemma funMap_add_to_add (M : BASICModel) (x y : M.num) :
  M.hPeano.funMap PeanoFunc.add ![x, y] = x + y := rfl
@[simp] lemma funMap_mul_to_mul (M : BASICModel) (x y : M.num) :
  M.hPeano.funMap PeanoFunc.mul ![x, y] = x * y := rfl
@[simp] lemma funMap_zero_to_zero (M : BASICModel) :
  M.hPeano.funMap PeanoFunc.zero ![] = (0 : M.num) := rfl
@[simp] lemma funMap_one_to_one (M : BASICModel) :
  M.hPeano.funMap PeanoFunc.one ![] = (1 : M.num) := rfl

@[simp] lemma RelMap_leq_to_leq (M : BASICModel) (x y : M.num) :
  M.hPeano.RelMap PeanoRel.leq ![x, y] <-> x <= y := Eq.to_iff rfl

instance {k} (M : BASICModel) : Inhabited (Fin k -> M.num) where
  default _ := M.hPeano.funMap PeanoFunc.zero Fin.elim0

-- instance (M : BASICModel) : Inhabited (Fin 0 -> M.num) where
--   default := Fin.elim0

-- abbrev BASICModel.add := BASICModel.

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)
-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
@[simp] def mkInductionSentence {n} {a} {k} (h : a ≃ Fin k) (phi: peano.BoundedFormula (DisplayedFV1 ⊕ a) n) : peano.Sentence :=
  let univ := (phi.alls.iAllsComputable h)
  let x := (peano.var DisplayedFV1.x)

  let base := univ.subst (fun _ => 0)

  let step_assumption := univ
  let step_target := univ.subst (fun _ => x + 1)
  let step' : peano.Formula DisplayedFV1 := step_assumption ⟹ step_target
  let step := iAllsFv1 step'

  let forall_x_holds := iAllsFv1 univ
  base ⟹ step ⟹ forall_x_holds

structure IOPENModel extends BASICModel where
  open_induction {a} {k}
    (phi : peano.BoundedFormula (DisplayedFV1 ⊕ a) 0)
    (h : a ≃ Fin k) :
    phi.isOpen -> (mkInductionSentence h phi).Realize num


-- TODO: define it to use 'induction' tactic straight from Lean
-- def IOPENModel.OpenRec {M : IOPENModel} {a : Type} {k}
--   (phi : peano.BoundedFormula (DisplayedFV1 ⊕ a) 0)
--   (h : a ≃ Fin k)
--   (hOpen : phi.isOpen)
--   {P : M.num -> Prop}
--   (base : P 0)
--   (step: ∀ n, P n -> P (n + 1)) :
--   ∀ n, P n :=
-- by
--   let ind := M.open_induction phi
--   intro n


@[simp]
theorem BoundedFormula.relabel_sup {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabel g = (φ.relabel g) ⊔ (ψ.relabel g) :=
  rfl

@[simp]
theorem BoundedFormula.relabel_inf {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabel g = (φ.relabel g) ⊓ (ψ.relabel g) :=
  rfl

theorem BoundedFormula.relabelEquiv_rel {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k} {ts : Fin k -> L.Term (a ⊕ Fin n)}
  : ((BoundedFormula.rel R ts).relabelEquiv g : L.BoundedFormula b n) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n))) : L.BoundedFormula b n) :=
by
  rfl

theorem BoundedFormula.terms_eq_rel_eq {L : Language} {k a n} {R : L.Relations k} (ts ts' : Fin k -> L.Term (a ⊕ Fin n)) : ts = ts' -> rel R ts = rel R ts' := by
  intro h
  exact congrArg (rel R) h


-- define transport across equality!
-- https://proofassistants.stackexchange.com/a/1745
theorem BoundedFormula.zero_add {L : Language} {α} {n} :
  L.BoundedFormula α n = L.BoundedFormula α (0 + n) :=
by
  rw [Nat.zero_add]

@[simp]
theorem BoundedFormula.castLE_zero_add {L : Language} {α} {n} (h : n ≤ 0 + n) (φ : L.BoundedFormula α n) : φ.castLE h = BoundedFormula.zero_add ▸ φ := by
  sorry

-- theorem BoundedFormula.relabel_rel' {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k} {ts : Fin k -> L.Term (a ⊕ Fin n)}
--   : ((BoundedFormula.rel R ts).relabel (fun fv => Sum.inl (g fv) : a -> b ⊕ Fin 0) : L.BoundedFormula b (0 + n)) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n))) : L.BoundedFormula b n).castLE (by exact Nat.le_add_left n 0) :=

theorem BoundedFormula.relabel_rel {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k} {ts : Fin k -> L.Term (a ⊕ Fin n)}
  : ((BoundedFormula.rel R ts).relabel (fun fv => Sum.inl (g fv) : a -> b ⊕ Fin 0) : L.BoundedFormula b (0 + n)) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n))) : L.BoundedFormula b n).castLE (by exact Nat.le_add_left n 0) :=
  -- : ((BoundedFormula.rel R ts).relabel (fun fv => Sum.inl (g fv) : a -> b ⊕ Fin 0) : L.BoundedFormula b (0 + n)) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n))) : L.BoundedFormula b n).castLE_zero_add :=
by
  -- rw [BoundedFormula.castLE_zero_add]
  apply BoundedFormula.terms_eq_rel_eq
  induction k with
  | zero => exact List.ofFn_inj.mp rfl
  | succ k ih =>
    funext i
    cases i using Fin.lastCases with
    | last => sorry
    | cast i => sorry
    -- | zero =>
    --   simp
    --   cases (ts 0) with
    --   | var t =>
    --     cases t with
    --     | inl nam => simp [relabelAux]
    --     | inr ind =>
    --       simp [relabelAux, Fin.castLE, Fin.cast]
    --   | @func l f f_ts =>
    --     simp [Term.relabel]
    --     induction l with
    --     | zero =>
    --     simp [relabelAux]
    --   congr
    --   unfold relabelAux
    --   funext x
    --   rw [Function.comp_apply]
    --   rw [Function.comp_apply]

    --   rw [Fin.castLE_of_eq]
    --   have aux : forall x, @Fin.cast n (0 + n) _ x = x := by
    --     sorry

    --   rw [aux]
    --   simp [Fin.cast]




  -- unfold Function.comp
  -- funext
  -- unfold relabelAux
  -- rw [Term.relabel]
  -- rw [Function.comp_apply]
  -- simp only [castLE]
  -- unfold Term.relabel
  -- unfold BoundedFormula.relabel mapTermRel relabelAux Term.relabel id



  -- simp only [id_eq, rel.injEq, heq_eq_eq, true_and]
  -- simp


  -- match k with
  -- | 0 => rw [BoundedFormula.relabel_]
  -- rw [BoundedFormula]

-- theorem BoundedFormula.relabel_rel {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k} {ts} {n l}
--   : ((BoundedFormula.rel R ts).relabel ((fun x : a => Sum.inl (g x)) : a -> b ⊕ (Fin n)) : L.BoundedFormula b n) = (BoundedFormula.rel R (fun i => ((ts i).relabel (Sum.map g id))) : L.BoundedFormula b n) :=
-- by
--   simp

-- theorem BoundedFormula.IsDelta0.relabelEquiv

theorem BoundedFormula.IsDelta0.relabel {a b} (phi : peano.Formula a) (g : a ≃ b): BoundedFormula.IsDelta0 phi -> BoundedFormula.IsDelta0 (phi.relabel g) :=
by
  intro h
  -- simp [BoundedFormula.relabelEquiv, mapTermRelEquiv]
  simp [Formula.relabel]
  cases phi with
  | falsum =>
    constructor
    simp only [relabel_falsum, Nat.add_zero]
    constructor
  | equal =>
    constructor
    apply BoundedFormula.IsQF.relabel
    cases h
    assumption
  | rel =>
    constructor
    apply BoundedFormula.IsQF.relabel
    cases h
    assumption
  | imp pre post =>
    rw [<- BoundedFormula.IsDelta0.imp.mpr] at h
    apply BoundedFormula.IsDelta0.imp
    · apply BoundedFormula.IsDelta0.relabel
      exact h.left
    · apply BoundedFormula.IsDelta0.relabel
      exact h.right
  | ex f =>
    -- rw [BoundedFormula.relabel_ex]
    cases h with
    | of_isQF h' =>
      cases h' with
      | of_isAtomic h'' =>
        cases h''
    | bdEx phi t =>
      rw [BoundedFormula.relabel_ex]
      rw [BoundedFormula.relabel_inf]
      rw [BoundedFormula.relabel_inf]

      -- here we need to prove some lemma using BoundedFormula.mapTermRel
      sorry
      -- conv => arg 1; rhs; lhs; arg 2; rw [BoundedFormula.relabel_rel g]
      -- apply BoundedFormula.IsDelta0.relabel
      -- apply BoundedFormula.IsDelta0.bdEx
  | all =>
    sorry

variable (L : Language) (α β n)

@[simp]
theorem BoundedFormula.relabelEquiv_falsum (g : α ≃ β) {k} :
    (falsum : L.BoundedFormula α k).relabelEquiv g = falsum :=
  rfl

@[simp]
theorem BoundedFormula.relabelEquiv_all {L : Language} {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabelEquiv g = (φ.relabelEquiv g).all := by
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  simp only [Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk]
  conv => lhs; unfold mapTermRel
  simp

@[simp]
theorem BoundedFormula.relabelEquiv_ex {L : Language} {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabelEquiv g = (φ.relabelEquiv g).ex := by
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  simp only [Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk]
  conv => lhs; unfold mapTermRel
  simp

@[simp]
theorem BoundedFormula.relabelEquiv_imp (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabelEquiv g = (φ.relabelEquiv g).imp (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem BoundedFormula.relabelEquiv_inf (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊓ (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem BoundedFormula.relabelEquiv_sup (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊔ (ψ.relabelEquiv g) :=
  rfl

theorem BoundedFormula.IsAtomic.relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α ≃ β) : (φ.relabelEquiv f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

@[simp]
theorem BoundedFormula.IsQF.imp.mpr {L : Language} {α} {m} {φ ψ : L.BoundedFormula α m} :
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

theorem BoundedFormula.IsQF.relabelEquiv.mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : φ.IsQF) :
    (φ.relabelEquiv f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabelEquiv f).isQF) fun _ _ h1 h2 => h1.imp h2

open BoundedFormula
theorem BoundedFormula.IsQF.relabelEquiv.mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : (φ.relabelEquiv f).IsQF) :
    φ.IsQF := by
  induction φ with
  | falsum => constructor
  | equal => constructor; constructor
  | imp pre post h_pre h_post =>
    apply IsQF.imp
    · apply h_pre
      rw [relabelEquiv_imp] at h
      rw [IsQF.imp.mpr] at h
      exact h.left
    · apply h_post
      rw [relabelEquiv_imp] at h
      rw [IsQF.imp.mpr] at h
      exact h.right
  | rel => constructor; constructor
  | all =>
    rw [BoundedFormula.relabelEquiv_all] at h
    cases h with
    | of_isAtomic h' => cases h'
  | ex =>
    rw [BoundedFormula.relabelEquiv_ex] at h
    cases h with
    | of_isAtomic h' => cases h'

theorem BoundedFormula.IsQF.relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsQF <-> φ.IsQF := ⟨IsQF.relabelEquiv.mpr f, IsQF.relabelEquiv.mp f⟩


theorem BoundedFormula.IsQF.mapTermRel {α β} {m : ℕ} {φ : peano.BoundedFormula α 0} {g : Nat -> Nat}  (ft: forall n, peano.Term (α ⊕ (Fin n)) -> peano.Term (β ⊕ Fin (g n))) (fr) (h) :
  (φ.mapTermRel ft fr h).IsQF <-> φ.IsQF := by
  sorry

@[simp]
theorem BoundedFormula.IsDelta0.mapTermRel (φ : peano.BoundedFormula α 0) {g : Nat -> Nat} {ft: forall n, peano.Term (α ⊕ (Fin n)) -> peano.Term (β ⊕ Fin (g n))} {fr} {h}:
    (φ.mapTermRel ft fr h).IsDelta0 <-> φ.IsDelta0 := by
  constructor
  · sorry
  · intro h'
    cases h' with
    | of_isQF h'' =>
      constructor
      -- TODO: this doesn't work if IsQF.mapTermRel is not narrowed
      -- down to 'peano' language only!
      -- rw [@IsQF.mapTermRel peano _ _ _ _ _ ft fr h]
      -- TODO: this doesn't work if IsQF.mapTermRel is not narrowed
      -- down to 'peano' language only!
      -- rw [<- BoundedFormula.IsQF.mapTermRel ft fr h] at h''
      rw [IsQF.mapTermRel]
      · exact h''
      · exact 0 -- why do we need to do this?
    | imp pre post =>
      apply IsDelta0.imp
      · rw [IsDelta0.mapTermRel]; exact pre
      · rw [IsDelta0.mapTermRel]; exact post
    | bdEx phi t =>
      unfold Formula.iBdExComputable Formula.iExsComputable
      unfold exs
      unfold exs
      rw [@relabel_inf]
      unfold BoundedFormula.mapTermRel
      unfold BoundedFormula.mapTermRel

      simp
      sorry
    | bdAll =>
      sorry

theorem BoundedFormula.IsDelta0.relabelEquiv {a b} (phi : peano.Formula a) (g : a ≃ b):
  BoundedFormula.IsDelta0 phi <-> BoundedFormula.IsDelta0 (phi.relabelEquiv g) :=
by
  cases phi with
  | falsum =>
    apply Iff.intro <;> (intro; constructor; constructor)
  | equal =>
    apply Iff.intro <;> (intro; constructor; constructor; constructor)
  | imp p q =>
    constructor
    · intro h
      rw [<- BoundedFormula.IsDelta0.imp.mpr] at h
      apply BoundedFormula.IsDelta0.imp
      · apply (BoundedFormula.IsDelta0.relabelEquiv _ g).mp
        exact h.left
      · apply (BoundedFormula.IsDelta0.relabelEquiv _ g).mp
        exact h.right
    · intro h
      rw [relabelEquiv_imp] at h
      cases h with
      | of_isQF h' =>
        cases h' with
        | of_isAtomic h'' =>
          cases h''
        | imp pre post =>
          constructor
          apply BoundedFormula.IsQF.imp
          · rw [IsQF.relabelEquiv] at pre; exact pre
          · rw [IsQF.relabelEquiv] at post; exact post
      | imp pre' post' =>
        apply IsDelta0.imp
        -- recursive call, but on a smaller formula!
        · rewrite [<- relabelEquiv] at pre'
          exact pre'
        · rewrite [<- relabelEquiv] at post'
          exact post'
  | rel =>
    constructor <;> (intro; constructor; constructor; constructor)
  | ex => sorry
  | all => sorry



-- HERE, PROVING STARTS! ---------------------------------------------------

attribute [simp] BoundedFormula.alls BoundedFormula.exs Sentence.Realize Formula.Realize Formula.relabel Fin.snoc

namespace IOPENModel

variable (M : IOPENModel.{_, _, _, 0})

-- page 36 of draft (47 of pdf)
-- Example 3.8 The following formulas (and their universal closures) are theorems of IOPEN:


-- TODO: not fixing the 'num'(?) universe level to 0 breaks everything.
-- learn how to do universe polymorphism properly and fix this

-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z
theorem add_assoc
  : ∀ x y z : M.num, (x + y) + z = x + (y + z) :=
by
  have ind := M.open_induction (display_z'' $ ((x'' + y'') + z'') =' (x'' + (y'' + z''))) DisplayedFV2.equivFin2 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  -- Simplify everything!
  have b2 := M.B2
  have b3 := M.B3
  have b4 := M.B4
  simp at ind b3 b4 b2 ⊢

  intro x y z
  -- Induction on z
  apply ind
  · intro x y
    rw [b3 (x + y)]
    rw [b3 y]
  · intro z hInd x y
    rw [b4]
    rw [b4]
    rw [b4]
    rw [<- (b2 (x + y + z) (x + (y + z)))]
    -- Option 0! :)
    rw [hInd]
    -- Option 1 (suggested by apply?):
    -- apply congrFun (congrArg HAdd.hAdd (hInd x y)) 1
    -- Option 2, more intuitively
    -- -- Auxiliary lemma (B2 in reverse) : x = y -> x + 1 = y + 1
    -- have b2_rev : forall (x y : M.num), x = y -> x + 1 = y + 1 := by {
    --   intro x' y' h
    --   rw [h]
    -- }
    -- apply b2_rev
    -- apply hInd

lemma add_0_comm
  : ∀ x : M.num, x + 0 = 0 + x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢
  have ind := M.open_induction (display_x ((x + 0) =' (0 + x))) Empty.equivFin0 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x
  apply ind
  intro a ha
  rw [<- add_assoc]
  rw [<- ha]
  rw [b3]
  rw [b3]

lemma add_1_comm
  : ∀ x : M.num, x + 1 = 1 + x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢
  have ind := M.open_induction (display_x ((x + 1) =' (1 + x))) Empty.equivFin0 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x
  apply ind
  · rw [c, b3]
  · intro a ha
    rw [<- add_assoc]
    rw [ha]

-- O2. x + y = y + x (Commutativity of +)
theorem add_comm
  : ∀ x y : M.num, x + y = y + x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  -- proof : induction on y, first establishing the special cases y = 0 and y = 1
  have ind := M.open_induction (display_y' ((x' + y') =' (y' + x'))) DisplayedFV1.equivFin1 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y
  apply ind
  · intro; rw [add_0_comm]
  · intro a hInd b
    rw [<- add_assoc]
    rw [hInd]
    rw [add_1_comm]
    rw [add_assoc]
    rw [hInd]

-- O3. x · (y + z) = (x · y) + (x · z) (Distributive law)
theorem mul_add
  : ∀ x y z : M.num, x * (y + z) = (x * y) + (x * z) :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  -- proof: induction on z
  have ind := M.open_induction (display_z'' $ (x'' * (y'' + z'')) =' ((x'' * y'') + (x'' * z''))) DisplayedFV2.equivFin2 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y z
  apply ind
  · intro a b
    rw [b3]
    rw [b5]
    rw [b3]
  · intro b hInd_b a2 a3
    rw [add_comm]
    rw [add_assoc]
    rw [add_comm]
    rw [hInd_b]
    conv => lhs; left; rw [add_comm]; rw [b6]
    rw [b6]
    conv => rhs; right; rw [add_comm]
    rw [add_assoc]

theorem mul_one
  : ∀ x : M.num, x * 1 = x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  intro x
  rw [<- c]
  rw [b6]
  rw [b5]
  rw [add_comm]
  rw [b3]

-- O4. (x · y) · z = x · (y · z) (Associativity of ·)
theorem mul_assoc
  : ∀ x y z : M.num, (x * y) * z = x * (y * z) :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  -- proof: induction on z, using O3
  have ind := M.open_induction (display_z'' $ (x'' * y'' * z'') =' (x'' * (y'' * z''))) DisplayedFV2.equivFin2 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y z
  apply ind
  · intro x y
    rw [b5]
    rw [b5]
    rw [b5]
  · intro x hInd_x y z
    rw [mul_add]
    rw [mul_add]
    rw [mul_one]
    rw [mul_one]
    rw [mul_add]
    rw [<- hInd_x]

lemma zero_mul
  : ∀ x : M.num, 0 * x = 0 :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.open_induction (display_x $ (0 * x) =' 0) Empty.equivFin0 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x
  apply ind
  · rw [b5]
  · intro x hInd_0_x
    rw [b6]
    rw [hInd_0_x]
    rw [b3]

lemma one_mul
  : ∀ x : M.num, 1 * x = x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.open_induction (display_x $ (1 * x) =' x) Empty.equivFin0 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x
  apply ind
  · rw [b5]
  · intro x hInd_1_x
    rw [b6]
    rw [hInd_1_x]

lemma mul_add_1_left
  : ∀ x y : M.num, (x + 1) * y = x * y + y :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢
  have ind := M.open_induction (display_y' $ ((x' + 1) * y') =' ((x' * y') + y')) DisplayedFV1.equivFin1 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y
  apply ind
  · intro y
    rw [c]
    rw [one_mul]
    rw [zero_mul]
    rw [<- add_0_comm]
    rw [b3]
  · intro y hInd_y x
    -- this was already proved and suddenly the proof's all wrong
    -- i made fat finger? or flakyness of `simp` with no `only`?
    rw [hInd_y]
    sorry
    -- conv => lhs; rw [add_assoc]; right; rw [<- add_assoc]; left; rw [add_comm]
    -- conv => rhs; rw [add_assoc]; right; rw [<- add_assoc]

-- O5. x · y = y · x (Commutativity of ·)
theorem mul_comm
  : ∀ x y : M.num, x * y = y * x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.open_induction (display_y' $ (x' * y') =' (y' * x')) DisplayedFV1.equivFin1 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y
  apply ind
  · intro x
    rw [b5]
    rw [zero_mul]
  · intro x hInd_x y
    rw [b6]
    rw [mul_add_1_left]
    rw [hInd_x]

-- O6. x + z = y + z → x = y (Cancellation law for +)
theorem add_cancel_right
  : ∀ x y z : M.num, x + z = y + z → x = y :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.open_induction (display_z'' $ ((x'' + z'') =' (y'' + z'') ⟹ (x'' =' y''))) DisplayedFV2.equivFin2 (by
    apply BoundedFormula.IsQF.imp
    · constructor
      apply BoundedFormula.IsAtomic.equal
    · constructor
      apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x y z
  apply ind
  · intro x y
    rw [b3]
    rw [b3]
    intro h
    exact h
  · intro x hInd_x y z
    conv => lhs; lhs; right; rw [add_comm]
    conv => lhs; rhs; right; rw [add_comm]
    rw [<- add_assoc]
    rw [<- add_assoc]
    intro h
    apply b2
    apply hInd_x
    exact h

-- O7. 0 ≤ x
theorem zero_le
  : ∀ x : M.num, 0 ≤ x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  intro x
  rw [<- b3 x]
  rw [add_comm]
  apply b8

-- O8. x ≤ 0 → x = 0
theorem le_zero_eq
  : ∀ x : M.num, x ≤ 0 → x = 0 :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  intro x h
  apply b7
  · exact h
  · apply zero_le

-- O9. x ≤ x
theorem le_refl
  : ∀ x : M.num, x ≤ x :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  intro x
  conv => right; rw [<- b3 x]
  apply b8

-- O10. x ≠ x + 1
theorem ne_succ
  : ∀ x : M.num, x ≠ x + 1 :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.open_induction (display_x $ x ≠' (x + 1)) Empty.equivFin0 (by
    apply BoundedFormula.IsQF.not
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  simp at ind

  intro x
  apply ind
  · intro h
    apply b1 0
    apply Eq.symm
    exact h
  · intro a h hq
    apply h
    apply b2
    exact hq

end IOPENModel

structure IDelta0Model extends BASICModel where
  delta0_induction {a} {k}
    (phi : peano.Formula (DisplayedFV1 ⊕ a))
    (h : a ≃ Fin k) :
    phi.IsDelta0 -> (mkInductionSentence h phi).Realize num

namespace IDelta0Model

-- Example 3.9 Theorems of IΔ0

-- D1. x ≠ 0 → ∃ y ≤ x, x = y + 1  (Predecessor)
theorem pred_exists (M : IDelta0Model.{_,_,_,0}) :
  ∀ x : M.num, x ≠ 0 → ∃ y, y ≤ x ∧ x = y + 1 :=
by
  have b1 := M.B1; have b2 := M.B2; have b3 := M.B3
  have b4 := M.B4; have b5 := M.B5; have b6 := M.B6
  have b7 := M.B7; have b8 := M.B8; have c := M.C
  simp at b1 b2 b3 b4 b5 b6 b7 b8 c ⊢

  have ind := M.delta0_induction (
    display_x $ (x ≠' 0) ⟹ Formula.iBdExComputable (x) (display_y' $ x' =' (y' + 1))
  ) Empty.equivFin0 (by
    unfold display_x
    rw [<- BoundedFormula.IsDelta0.relabelEquiv]
    apply BoundedFormula.IsDelta0.imp
    · constructor
      apply BoundedFormula.IsQF.not
      apply BoundedFormula.IsQF.of_isAtomic
      apply BoundedFormula.IsAtomic.equal
    · apply BoundedFormula.IsDelta0.iBdExComputable
  )
  simp at ind

  intro x
  apply ind
  · intro a ha ha'
    exists a
    constructor
    · apply b8
    · rfl

-- D2. ∃ z, (x + z = y ∨ y + z = x)
theorem add_diff_exists (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y : M.num, ∃ z, x + z = y ∨ y + z = x :=
by sorry

-- D3. x ≤ y ↔ ∃ z, x + z = y
theorem le_iff_exists_add (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y : M.num, x ≤ y ↔ ∃ z, x + z = y :=
by sorry

-- D4. (x ≤ y ∧ y ≤ z) → x ≤ z  (Transitivity)
theorem le_trans (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y z : M.num, x ≤ y ∧ y ≤ z → x ≤ z :=
by sorry

-- D5. x ≤ y ∨ y ≤ x  (Total order)
theorem le_total (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y : M.num, x ≤ y ∨ y ≤ x :=
by sorry

-- D6. x ≤ y ↔ x + z ≤ y + z
theorem le_add_right (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y z : M.num, x ≤ y ↔ x + z ≤ y + z :=
by sorry

-- D7. x ≤ y → x * z ≤ y * z
theorem le_mul_right (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y z : M.num, x ≤ y → x * z ≤ y * z :=
by sorry

-- D8. x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1)  (Discreteness 1)
theorem le_succ_iff (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y : M.num, x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1) :=
by sorry

-- D9. x < y ↔ x + 1 ≤ y  (Discreteness 2)
-- recall: x < y means x ≤ y ∧ x ≠ y
theorem lt_iff_succ_le (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y : M.num, (x ≤ y ∧ x ≠ y) ↔ x + 1 ≤ y :=
by sorry

-- D10. x * z = y * z ∧ z ≠ 0 → x = y  (Cancellation law for ·)
theorem mul_cancel_right (M : IDelta0Model.{_,_,_,0}) :
  ∀ x y z : M.num, (x * z = y * z ∧ z ≠ 0) → x = y :=
by sorry

end IDelta0Model
