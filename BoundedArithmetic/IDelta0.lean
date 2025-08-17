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

@[simp] def Language.peano : Language :=
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

def natToM {M} [h : Language.peano.Structure M] : Nat -> M
| 0 => 0
| 1 => 1
| n + 1 => natToM n + 1

instance {M} [h : Language.peano.Structure M] (n) : OfNat M n where
  ofNat := natToM n

namespace Language

namespace Formula
/-- Computable version of FirstOrder.Language.Formula.iAlls -/
@[simp] def iAllsComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

@[simp] def iAllsComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  (BoundedFormula.relabel (fun a => Sum.inr $ e a) φ).alls
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
@[simp] def Term.bdLt {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
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

end peano

namespace BoundedFormula

-- Definition 3.7, page 36 of draft (47 of pdf)
abbrev isOpen {a} {n} (formula : peano.BoundedFormula a n) := FirstOrder.Language.BoundedFormula.IsQF formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
inductive IsDelta0 {a : Type u} : {n : Nat} -> peano.BoundedFormula a n -> Prop
| of_isQF {phi} (h : BoundedFormula.IsQF phi) : IsDelta0 phi
| imp {phi1 phi2} (h1 : IsDelta0 phi1) (h2 : IsDelta0 phi2) : IsDelta0 (phi1.imp phi2)
| bdEx {n}
  {phi : peano.BoundedFormula a (n + 1)}  -- `x` is represented by label `Sum.inr n`
  {t : peano.Term (a ⊕ Fin n)} -- 'If the variable `x` does not occur in the term `t`'
  (h : IsDelta0 phi)
  :
  -- TODO: make it work in this alternative way
  -- IsDelta0 $ namedEx $
  --   ((Term.var (Sum.inl $ NameOrSpecial.special)) <=' (t.relabel $ Sum.map (fun n => NameOrSpecial.standard n) (Fin.succEmb n))) ⊓ phi
  IsDelta0 $ ∃' (
    (
      -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
      (&(Fin.last n))  -- lift `n` into Term.var; this denotes just `x`
      <='
      (t.relabel $ Sum.map id (Fin.succEmb n))  -- lift `t` from lv `n` to lv `n + 1`
    )
    ⊓ phi
  )

| bdAll {n}
  {phi : peano.BoundedFormula a (n + 1)}
  {t : peano.Term (a ⊕ Fin n)} -- 'If the variable `x` does not occur in the term `t`'...
  (h : IsDelta0 phi)
  :
  IsDelta0 $ ∀' (
    (&(Fin.ofNat (n + 1) n)) <=' (t.relabel $ Sum.map id (Fin.succEmb n))
    ⟹ phi
  )

end BoundedFormula

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

@[simp] def iAllsFv0 (phi: peano.Formula Empty) := phi.iAllsComputableEmpty Empty.equivFin0
@[simp] def iAllsFv1 (phi: peano.Formula DisplayedFV1) := phi.iAllsComputableEmpty DisplayedFV1.equivFin1
@[simp] def iAllsFv2 (phi: peano.Formula DisplayedFV2) := phi.iAllsComputableEmpty DisplayedFV2.equivFin2
@[simp] def iAllsFv3 (phi: peano.Formula DisplayedFV3) := phi.iAllsComputableEmpty DisplayedFV3.equivFin3

@[simp] def x {k} : peano.Term (DisplayedFV1 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV1.x)
@[simp] def x' {k} : peano.Term (DisplayedFV2 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV2.x)
@[simp] def y' {k} : peano.Term (DisplayedFV2 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV2.y)
@[simp] def x'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.x)
@[simp] def y'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.y)
@[simp] def z'' {k} : peano.Term (DisplayedFV3 ⊕ Fin k) := (peano.var $ Sum.inl DisplayedFV3.z)

-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
@[simp] def B1_ax : peano.Formula DisplayedFV1 := (x + 1) ≠' 0
@[simp] def B2_ax : peano.Formula DisplayedFV2 := (x' + 1) =' (y' + 1) ⟹ x' =' y'
@[simp] def B3_ax : peano.Formula DisplayedFV1 := (x + 0) =' x
@[simp] def B4_ax : peano.Formula DisplayedFV2 := (x' + (y' + 1)) =' ((x' + y') + 1)
@[simp] def B5_ax : peano.Formula DisplayedFV1 := (x * 0) ≠' 0
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
    (phi : peano.Formula (DisplayedFV1 ⊕ a))
    (h : a ≃ Fin k) :
    phi.isOpen -> (mkInductionSentence h phi).Realize num

-- cant; fucking make this work idk why
-- def IOPENModel.ind_x (M : IOPENModel) (phi : peano.Formula DisplayedFV1) (h: phi.isOpen) : Prop :=
--   let relabeled : peano.Formula (DisplayedFV1 ⊕ Empty) := phi.relabel (fun fv => match fv with | .x => Sum.inl fv)
--   let h' : relabeled.isOpen := by {
--     unfold BoundedFormula.isOpen at h
--     unfold BoundedFormula.isOpen
--     apply BoundedFormula.IsQF.relabel
--     exact h
--   }
--   M.open_induction relabeled Empty.equivFin0 h'

-- def IOPENModel.ind_x' (M : IOPENModel) (phi : peano.Formula DisplayedFV2) :=
--   M.open_induction (phi.relabel (fun fv => match fv with
--   | .x => Sum.inl .x
--   | .y => Sum.inr .x -- it will be quantified over anyway
--   )) DisplayedFV1.equivFin1

def display_x (phi : peano.Formula DisplayedFV1) : peano.Formula (DisplayedFV1 ⊕ Empty) :=
  phi.relabel (fun fv => match fv with
  | .x => Sum.inl .x
  )

@[simp]
def display_z'' {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV2) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inr DisplayedFV2.x
  | .y => Sum.inr DisplayedFV2.y
  | .z => Sum.inl DisplayedFV1.x
  )) : DisplayedFV3 -> ((DisplayedFV1 ⊕ DisplayedFV2) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
theorem distr {T T'} (v : T -> T') (f1 f2 f3: DisplayedFV3 -> T)
  : v ∘ (fun fv : DisplayedFV3 => match fv with |.x => f1 .x |.y => f2 .y | .z => f3 .z)
  = (fun fv : DisplayedFV3 => match fv with |.x => v (f1 .x) |.y => v (f2 .y) | .z => v ( f3 .z)) := by
  ext a; cases a <;> simp

@[simp]
theorem realize_fun_eq {L : Language} {M} [L.Structure M] {α} {n} {φ : L.BoundedFormula α n} {v v' : α → M} {xs} : (h : v = v') -> (φ.Realize v xs ↔ φ.Realize v' xs) := by
  intro h
  rw [h]

@[simp]
theorem realize_fun_eq' {L : Language} {M} [L.Structure M] {α} {n} {φ : L.BoundedFormula α n} {v v' : α → M} {xs xs'}: (h : v = v') -> (h' : xs = xs') -> (φ.Realize v xs ↔ φ.Realize v' xs') := by
  intro h h'
  rw [h, h']

@[simp] theorem Formula.eq_BoundedFormula {L} {a} :
  Formula L a = BoundedFormula L a 0 := rfl

@[simp]
theorem BoundedFormula.realize_display_z'' {M} [peano.Structure M] {n} {φ : peano.BoundedFormula DisplayedFV3 n} {v : _ → M} {xs}
    : BoundedFormula.Realize (display_z'' φ) v xs ↔
      φ.Realize (fun fv => match fv with | .x => v (Sum.inr .x) | .y => v (Sum.inr .y) | .z => v (Sum.inl .x)) xs := by
  unfold display_z''
  rw [@BoundedFormula.realize_castLE_of_eq _ _ _ _ (0 + n) n (by simp only [Nat.zero_add])]
  rw [BoundedFormula.realize_relabel]
  apply realize_fun_eq'
  · apply (distr v (fun _ => Sum.inr DisplayedFV2.x) (fun _ => Sum.inr DisplayedFV2.y) (fun _ => Sum.inl DisplayedFV1.x))
  · rw [Fin.natAdd_zero]
    rfl

@[simp]
theorem Formula.realize_display_z'' {M} [peano.Structure M] {φ} {v : _ → M}
    : Formula.Realize (display_z'' φ) v ↔
      Formula.Realize φ (fun fv => match fv with | .x => v (Sum.inr .x) | .y => v (Sum.inr .y) | .z => v (Sum.inl .x)) := by
  unfold display_z''
  unfold Formula.Realize
  rw [@BoundedFormula.realize_castLE_of_eq _ _ _ _ 0 0 rfl]
  rw [BoundedFormula.realize_relabel]
  apply realize_fun_eq
  apply (distr v (fun _ => Sum.inr DisplayedFV2.x) (fun _ => Sum.inr DisplayedFV2.y) (fun _ => Sum.inl DisplayedFV1.x))


-- Example 3.8 The following formulas (and their universal closures) are theorems of IOPEN:
-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z

@[simp] def add_assoc_frm : peano.Formula DisplayedFV3 := ((x'' + y'') + z'') =' (x'' + (y'' + z''))

theorem iopen_add_assoc_iff {M : IOPENModel}
  : FirstOrder.Language.Sentence.Realize M.toBASICModel.num (iAllsFv3 add_assoc_frm)
    <-> ∀ x y z : M.num, (x + y) + z = x + (y + z)
  := by
  simp only [peano, iAllsFv3, Formula.iAllsComputableEmpty, Nat.add_zero, DisplayedFV3.equivFin3,
    Fin.isValue, Equiv.coe_fn_mk, add_assoc_frm, peano.instAddTerm, x'', y'', z'']
  unfold HAdd.hAdd instHAdd Add.add
  apply Iff.intro
  · intro h x y z
    specialize h x y z
    simp only [Nat.reduceAdd, Fin.isValue, BoundedFormula.realize_relabel, Nat.add_zero,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, BoundedFormula.realize_bdEqual,
      Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl, Function.comp_apply,
      Sum.elim_inr, Fin.snoc_apply_zero, funMap_add_to_add] at h
    exact h
  · intro h x y z
    specialize h x y z
    simp only [Nat.reduceAdd, Fin.isValue, BoundedFormula.realize_relabel, Nat.add_zero,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, BoundedFormula.realize_bdEqual,
      Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl, Function.comp_apply,
      Sum.elim_inr, Fin.snoc_apply_zero, funMap_add_to_add]
    exact h

@[simp] lemma Term.realize_add {a} {M} [h : peano.Structure M] {env} {t u : peano.Term a} :
    Term.realize env (t + u) = h.funMap PeanoFunc.add ![Term.realize env t, Term.realize env u] := by
  simp [HAdd.hAdd]

theorem Formula.relabel_falsum {L : Language} {a b} (g : a -> b ⊕ Fin 0) :
  (.falsum : L.Formula a).relabel g = .falsum :=
  rfl

theorem BoundedFormula.relabel_bdEqual {L : Language} {a b} {n} (f : a -> b ⊕ (Fin n)) {k} (phi psi : L.Term (a ⊕ Fin k)) :
  ((phi =' psi).relabel f : L.BoundedFormula b (n + k)) = (phi.relabel (fun fv => BoundedFormula.relabelAux f k fv)) =' (psi.relabel (fun fv => BoundedFormula.relabelAux f k fv)) := by
  rfl

theorem Formula.relabel_bdEqual {L : Language} {a b} {n} (f : a -> b ⊕ (Fin n)) (phi psi : L.Term (a ⊕ Fin 0)) :
  ((phi =' psi : L.Formula a).relabel f : L.BoundedFormula b (n + 0)) = (phi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) =' (psi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) := by
  rfl

-- TODO: not fixing the 'num'(?) universe level to 0 breaks everything.
-- learn how to do universe polymorphism properly and fix this
theorem iopen_add_assoc (M : IOPENModel.{_, _, _, 0}) : FirstOrder.Language.Sentence.Realize M.toBASICModel.num (iAllsFv3 add_assoc_frm) := by
  have ind := M.open_induction (display_z'' add_assoc_frm) DisplayedFV2.equivFin2 (by
    constructor
    apply BoundedFormula.IsAtomic.equal
  )
  unfold mkInductionSentence Formula.iAllsComputable at ind
  unfold Sentence.Realize Formula.Realize at ind
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp] at ind

  -- Transform the base of induction
  conv at ind =>
    lhs
    rw [BoundedFormula.realize_subst]
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_display_z'']
    unfold add_assoc_frm
    rw [BoundedFormula.realize_bdEqual]
    unfold x'' y'' z'' HAdd.hAdd Add.add instHAdd
    simp [Fin.snoc]

  -- Transform the induction
  conv at ind =>
    rhs; lhs;
    unfold iAllsFv1 Formula.iAllsComputableEmpty
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    rw [BoundedFormula.realize_imp]

  -- Transform precondition of step of induction
  conv at ind =>
    rhs; lhs; intro; lhs
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro y
    rw [BoundedFormula.realize_all]
    intro z
    rw [BoundedFormula.realize_relabel]
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_display_z'']
    unfold add_assoc_frm x'' y'' z'' HAdd.hAdd Add.add instHAdd
    simp [Fin.snoc]

  -- Transform postcondition of step of induction
  conv at ind =>
    rhs; lhs; intro; rhs
    rw [BoundedFormula.realize_subst]
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_display_z'']
    unfold add_assoc_frm x'' y'' z'' HAdd.hAdd Add.add instHAdd
    simp [Fin.snoc]

  -- Transform the target of induction
  conv at ind =>
    rhs; rhs
    unfold iAllsFv1 Formula.iAllsComputableEmpty
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold BoundedFormula.alls
    rw [BoundedFormula.realize_display_z'']
    unfold add_assoc_frm x'' y'' z'' HAdd.hAdd Add.add instHAdd
    simp [Fin.snoc]

  -- Transform the actual target
  unfold iAllsFv3 Formula.iAllsComputableEmpty
  unfold BoundedFormula.alls
  unfold Sentence.Realize Formula.Realize
  unfold BoundedFormula.alls
  unfold BoundedFormula.alls
  unfold BoundedFormula.alls
  rw [BoundedFormula.realize_all]
  intro
  rw [BoundedFormula.realize_all]
  intro
  rw [BoundedFormula.realize_all]
  intro
  rw [BoundedFormula.realize_relabel]
  unfold add_assoc_frm x'' y'' z'' HAdd.hAdd instHAdd
  simp [Fin.snoc]

  -- Transform axioms
  have b3 := M.B3
  conv at b3 =>
    simp only [iAllsFv1, Formula.iAllsComputableEmpty]
    repeat unfold BoundedFormula.alls
    unfold Sentence.Realize Formula.Realize
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold B3_ax x HAdd.hAdd instHAdd
    simp [Fin.snoc]

  have b4 := M.B4
  conv at b4 =>
    simp only [iAllsFv2, Formula.iAllsComputableEmpty]
    repeat unfold BoundedFormula.alls
    unfold Sentence.Realize Formula.Realize
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold B4_ax x HAdd.hAdd instHAdd
    simp [Fin.snoc]

  have b2 := M.B2
  conv at b2 =>
    simp only [iAllsFv2, Formula.iAllsComputableEmpty]
    repeat unfold BoundedFormula.alls
    unfold Sentence.Realize Formula.Realize
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold B2_ax x HAdd.hAdd instHAdd
    simp [Fin.snoc]

  -- Actual proof! ----------------------------------
  -- Induction on z
  apply ind

  -- Prove base
  · intro x y
    rw [b3 (x + y)]
    rw [b3 y]

  -- Prove step
  · intro z hInd x y
    conv =>
      lhs
      rw [b4]
    conv =>
      rhs
      rw [b4]
      rw [b4]
    rw [<- (b2 (x + y + z) (x + (y + z)))]

    -- Auxiliary lemma (B2 in reverse) : x = y -> x + 1 = y + 1
    have b2_rev : forall (x y : M.num), x = y -> x + 1 = y + 1 := by {
      intro x' y' h
      rw [h]
    }
    apply b2_rev
    apply hInd


    -- Alternatively (suggested by apply?):
    -- exact congrFun (congrArg HAdd.hAdd (hInd x y)) 1

-- structure IDelta0Model extends BASICModel where
--   delta0_induction {n} :
--     ∀ (phi_syntax : peano.BoundedFormula Empty (n + 1)),
--     isDelta0 phi_syntax ->
--     -- phi(0)
--     realize_at toBASICModel phi_syntax zero ->
--     -- (∀ x : num, φ x -> φ (add x one)) ->
--     (forall x : num,
--       realize_at toBASICModel phi_syntax x ->
--       realize_at toBASICModel phi_syntax (add x one)
--     ) ->
--     -- ∀ x, φ x
--     (forall x : num, realize_at toBASICModel phi_syntax x)


-- -- Section 3.3.3 Defining y=2^x and BIT(i, x) in IDelta0 (Draft; p.53 of draft, p.64 of pdf)

-- -- Limited subtraction: The function x -' y := max(0, x - y) is Delta0-definable in IDelta0
-- -- First, define the relation by the defining axiom
-- def limited_subtraction_graph_def {a} (x y z : peano.Term a) :=
--   max ((y + z = x)) (x <= y ∧ z = 0)

-- -- z = x -' y IFF ( (y+z=x) or (x <= y AND z = 0)) IFF phi(x, y, z)
-- -- Then prove uniqueness
-- IDelta0 proves forall x, forall y, e! z, phi(x, y, z)



-- relation y = 2^x is Delta0-definable in IDelta0, but function f(x)=2^x is not Sigma1-def.!

-- CONSERVATIVE EXTENSION: in the definition of new structure, allow symbols in the peanouage,
-- which are definable in IDelta0! this will allow us to make induction over formulas
-- with new symbols



-- Example 3.9 The following formulas (and their universal closures) are theorems of IDelta0:
-- D1. x neq 0 -> Exists y<=x . (x = y + 1) (Predecessor)
-- proof: induction on x
-- def pred_form :=
--   -- let x := var_term (1 : Fin 2)
--   -- let y := var_term (0 : Fin 2) -- y will actually be bound by a quatifier
--   let xneq0 := BoundedFormula.not $ BoundedFormula.equal (var_term (0 : Fin 2)) (const_term funcZero) -- here 'y' means actually our 'x'!!!! (deBruijn indices)
--   let rhs : peano.BoundedFormula Empty 2 := BoundedFormula.ex
--     (max
--       (BoundedFormula.rel relationLeq ![var_term (0 : Fin 2), var_term (1 : Fin 2)])
--       (BoundedFormula.equal
--         (var_term (1 : Fin 2))
--         (Term.func funcAdd ![var_term (0 : Fin 2), const_term funcOne]))
--     )
--   imp_form xneq0 rhs

-- def pred_form_shallow (M : IDelta0Model) := ∀ x, (x ≠ M.zero) -> ∃ y , (M.leq y x ∧ x = M.add x M.one)

-- def pred_form_deep (M : IDelta0Model) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (pred_form.alls) (Empty.elim) ![]

-- theorem idelta0_pred_iff (M : IDelta0Model) : pred_form_shallow M <-> pred_form_deep M := by {
--   apply Iff.intro
--   · intro h
--     unfold pred_form_deep
--     unfold pred_form
--     simp [BoundedFormula.Realize, eq_form, binary_func_term, var_term]
--     repeat unfold BoundedFormula.alls
--     simp
--     unfold pred_form_shallow at h
--     intros x y z
--     specialize h y
--     rw [<- Term.bdEqual]
--     simp
--     simp [FirstOrder.peanouage.Structure.funMap, Fin.snoc]
--     sorry
--   · sorry
-- }


-- D2. Exists z . (x + z = y or y + z = x)
-- proof: induction on x. Base case: B2, O2. Induction step: B3, B4, D1
-- def symm_diff_form :=
--   let
-- def add_assoc_frm :=
-- -- deBruijn indices
--   let x := var_term (2 : Fin 3)
--   let y := var_term (1 : Fin 3)
--   let z := var_term (0 : Fin 3)
--   let lhs := binary_func_term Functions2.add (binary_func_term Functions2.add x y) z
--   let rhs := binary_func_term Functions2.add x (binary_func_term Functions2.add y z)
--   eq_form lhs rhs

-- def add_assoc_frm_shallow (M : IOPENModel) := ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)

-- def add_assoc_frm_deep (M : IOPENModel) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_frm.alls) (Empty.elim) ![]

-- Exercise 3.10 Show that IDelta0 proves the division theorem:
-- IDelta0 |- Forall x y (0 < x -> Exists q . Exists (r < x) . y = x * q + r)

-- def division_form :=
--   let x := var_term (2 : Fin 3)
--   let y := var_term (1 : Fin 3)
--   let z := var_term (0 : Fin 3)
--   let lhs := binary_func_term Functions2.add (binary_func_term Functions2.add x y) z
--   let rhs := binary_func_term Functions2.add x (binary_func_term Functions2.add y z)
--   eq_form lhs rhs

-- def add_assoc_frm_shallow (M : IOPENModel) := ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)

-- def add_assoc_frm_deep (M : IOPENModel) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_frm.alls) (Empty.elim) ![]


-- Example 5.44 (The Pairing Function). We define the pairing function
-- ⟨x, y⟩ as the following term of IΔ₀:

-- Exercise 5.45 Show using the results in Section 3.1 that IΔ₀ proves ⟨x, y⟩
-- is a one-one function. That is

-- def IDelta0Model.idelta0_pair x y :=

--   IDelta0Model.mul x y

-- theorem idelta0_pair_one_one (M : IDelta0Model) : forall x1 x2 y1 y2, ⟨x1, y1⟩ = ⟨x2, y2⟩ -> (x1 = x2 ∧ y1 = y2) := by
--   sorry
-- -- (First show that the LHS implies x₁ + y₁ = x₂ + y₂)
