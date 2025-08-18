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

@[simp]
theorem realize_iInfComputable {L : Language} {M} [L.Structure M] {α β} {n} {k} (e : β ≃ Fin k) {f : β → L.BoundedFormula α n}
    {v : α → M} {v' : Fin n → M} :
    (iInfComputable e f).Realize v v' ↔ ∀ b, (f b).Realize v v' := by
  simp only [iInfComputable, Finset.toListComputable, List.map_ofFn,
    BoundedFormula.realize_foldr_inf, List.mem_ofFn, Function.comp_apply, forall_exists_index,
    forall_apply_eq_imp_iff]
  rw [Equiv.forall_congr' e.symm]
  rw [@_root_.Equiv.symm_symm]
  rw [<- e.invFun_as_coe]
  rw [<- e.toFun_as_coe]
  intro
  rw [<- Function.comp_apply (f := e.invFun) (g := e.toFun)]
  rw [e.left_inv.id]
  rfl

-- @[simp]
-- theorem realize_iAllsComputable {L : Language} {M} [L.Structure M] {α β} {n} {k} (e : β ≃ Fin k) {f : L.Formula (α ⊕ β)}
--     {v : α → M} :
--     (iAllsComputable e f).Realize v ↔ ∀ b, (f b).Realize v := by
--   simp only [iInfComputable, Finset.toListComputable, List.map_ofFn,
--     BoundedFormula.realize_foldr_inf, List.mem_ofFn, Function.comp_apply, forall_exists_index,
--     forall_apply_eq_imp_iff]
--   rw [Equiv.forall_congr' e.symm]
--   rw [@_root_.Equiv.symm_symm]
--   rw [<- e.invFun_as_coe]
--   rw [<- e.toFun_as_coe]
--   intro
--   rw [<- Function.comp_apply (f := e.invFun) (g := e.toFun)]
--   rw [e.left_inv.id]
--   rfl

@[simp] def iExsUniqueComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExsComputable e <| φ ⊓ iAllsComputable e
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInfComputable e fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

@[simp] def iExsUniqueComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  iExsComputableEmpty e <| φ ⊓ iAllsComputable e
    ((φ.relabel (fun a => .inr a)).imp <|
      .iInfComputable e fun g => Term.equal (var (.inr g)) (var (.inl g)))

@[simp] def iBdExsUniqueComputable {α β} {k} (e : β ≃ Fin k) (bdTerms : β -> peano.Term (α ⊕ Fin 0)) (φ : peano.Formula (α ⊕ β)) : peano.Formula α :=
  let φ' : peano.Formula (α ⊕ β) := (Formula.iInfComputable e fun g => BoundedFormula.rel PeanoRel.leq ![var (.inl (.inr g)), (bdTerms g).relabel (Sum.map (fun c => .inl c) id)]) ⊓ φ
  iExsComputable e <| φ' ⊓ iAllsComputable e
    ((φ'.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInfComputable e fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

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
def Term.bdNeq {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  ∼(t1 =' t2)

/-- The less-than-or-equal relation of two terms as a bounded formula -/
def Term.bdLeq {a : Type u} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
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
@[simp] def iExsUniqueFv1 {a} (phi: peano.Formula (a ⊕ DisplayedFV1)) := phi.iExsUniqueComputable DisplayedFV1.equivFin1
@[simp] def iBdExsUniqueFv1 {a} (phi: peano.Formula (a ⊕ DisplayedFV1)) (terms : DisplayedFV1 -> peano.Term (a ⊕ Fin 0)) := phi.iBdExsUniqueComputable DisplayedFV1.equivFin1 terms

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

def display_x' {n} (phi : peano.BoundedFormula DisplayedFV2 n) : peano.BoundedFormula (DisplayedFV1 ⊕ DisplayedFV1) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inr .x
  | .y => Sum.inl .x
  )) : DisplayedFV2 -> ((DisplayedFV1 ⊕ DisplayedFV1) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
def display_x'' {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV2 ⊕ DisplayedFV1) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inr DisplayedFV1.x
  | .y => Sum.inl DisplayedFV2.x
  | .z => Sum.inl DisplayedFV2.y
  )) : DisplayedFV3 -> ((DisplayedFV2 ⊕ DisplayedFV1) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
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
def display_z''2 {n} (phi : peano.BoundedFormula DisplayedFV3 n) : peano.BoundedFormula (DisplayedFV2 ⊕ DisplayedFV1) n :=
  (phi.relabel ((fun fv => Sum.inl (match fv with
  | .x => Sum.inl DisplayedFV2.x
  | .y => Sum.inl DisplayedFV2.y
  | .z => Sum.inr DisplayedFV1.x
  )) : DisplayedFV3 -> ((DisplayedFV2 ⊕ DisplayedFV1) ⊕ Fin 0))).castLE (by
    simp only [Nat.zero_add]
    rfl
  )

@[simp]
theorem distr2 {T T'} (v : T -> T') (f1 f2: DisplayedFV2 -> T)
  : v ∘ (fun fv : DisplayedFV2 => match fv with |.x => f1 .x |.y => f2 .y )
  = (fun fv : DisplayedFV2 => match fv with |.x => v (f1 .x) |.y => v (f2 .y)) := by
  ext a; cases a <;> simp

@[simp]
theorem distr3 {T T'} (v : T -> T') (f1 f2 f3: DisplayedFV3 -> T)
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
theorem BoundedFormula.realize_display_x' {M} [peano.Structure M] {n} {φ : peano.BoundedFormula DisplayedFV2 n} {v : _ → M} {xs}
    : BoundedFormula.Realize (display_x' φ) v xs ↔
      φ.Realize (fun fv => match fv with | .x => v (Sum.inr .x) | .y => v (Sum.inl .x)) xs := by
  unfold display_x'
  rw [@BoundedFormula.realize_castLE_of_eq _ _ _ _ (0 + n) n (by simp only [Nat.zero_add])]
  rw [BoundedFormula.realize_relabel]
  apply realize_fun_eq'
  · apply (distr2 v (fun _ => Sum.inr DisplayedFV1.x) (fun _ => Sum.inl DisplayedFV1.x))
  · rw [Fin.natAdd_zero]
    rfl

@[simp]
theorem BoundedFormula.realize_display_z'' {M} [peano.Structure M] {n} {φ : peano.BoundedFormula DisplayedFV3 n} {v : _ → M} {xs}
    : BoundedFormula.Realize (display_z'' φ) v xs ↔
      φ.Realize (fun fv => match fv with | .x => v (Sum.inr .x) | .y => v (Sum.inr .y) | .z => v (Sum.inl .x)) xs := by
  unfold display_z''
  rw [@BoundedFormula.realize_castLE_of_eq _ _ _ _ (0 + n) n (by simp only [Nat.zero_add])]
  rw [BoundedFormula.realize_relabel]
  apply realize_fun_eq'
  · apply (distr3 v (fun _ => Sum.inr DisplayedFV2.x) (fun _ => Sum.inr DisplayedFV2.y) (fun _ => Sum.inl DisplayedFV1.x))
  · rw [Fin.natAdd_zero]
    rfl

@[simp]
theorem BoundedFormula.realize_display_z''2 {M} [peano.Structure M] {n} {φ : peano.BoundedFormula DisplayedFV3 n} {v : _ → M} {xs}
    : BoundedFormula.Realize (display_z''2 φ) v xs ↔
      φ.Realize (fun fv => match fv with | .x => v (Sum.inl .x) | .y => v (Sum.inl .y) | .z => v (Sum.inr .x)) xs := by
  unfold display_z''2
  rw [@BoundedFormula.realize_castLE_of_eq _ _ _ _ (0 + n) n (by simp only [Nat.zero_add])]
  rw [BoundedFormula.realize_relabel]
  apply realize_fun_eq'
  · apply (distr3 v (fun _ => Sum.inl DisplayedFV2.x) (fun _ => Sum.inl DisplayedFV2.y) (fun _ => Sum.inr DisplayedFV1.x))
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
  apply (distr3 v (fun _ => Sum.inr DisplayedFV2.x) (fun _ => Sum.inr DisplayedFV2.y) (fun _ => Sum.inl DisplayedFV1.x))


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

-- @[simp] lemma Term.realize_add {a} {M} [h : peano.Structure M] {env} {t u : peano.Term a} :
--     Term.realize env (t + u) = h.funMap PeanoFunc.add ![Term.realize env t, Term.realize env u] := by
--   simp [HAdd.hAdd]

theorem Formula.relabel_falsum {L : Language} {a b} (g : a -> b ⊕ Fin 0) :
  (.falsum : L.Formula a).relabel g = .falsum :=
  rfl

theorem BoundedFormula.relabel_bdEqual {L : Language} {a b} {n} (f : a -> b ⊕ (Fin n)) {k} (phi psi : L.Term (a ⊕ Fin k)) :
  ((phi =' psi).relabel f : L.BoundedFormula b (n + k)) = (phi.relabel (fun fv => BoundedFormula.relabelAux f k fv)) =' (psi.relabel (fun fv => BoundedFormula.relabelAux f k fv)) := by
  rfl

-- theorem Formula.relabel_bdEqual' {L : Language} {a b} {n} (f : a -> b) {k} (phi psi : L.Term a) :
--   ((Term.equal phi psi).relabel f : L.Formula b) = (phi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) =' (psi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) := by
--   rfl

theorem Formula.relabel_bdEqual {L : Language} {a b} {n} (f : a -> b ⊕ (Fin n)) (phi psi : L.Term (a ⊕ Fin 0)) :
  ((phi =' psi : L.Formula a).relabel f : L.BoundedFormula b (n + 0)) = (phi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) =' (psi.relabel (fun fv => BoundedFormula.relabelAux f 0 fv)) := by
  rfl

@[simp]
theorem BoundedFormula.relabel_sup {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabel g = (φ.relabel g) ⊔ (ψ.relabel g) :=
  rfl

@[simp]
theorem BoundedFormula.relabel_inf {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabel g = (φ.relabel g) ⊓ (ψ.relabel g) :=
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
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [display_z'', add_assoc_frm, x'', y'', z'']
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  -- Transform the induction
  conv at ind =>
    rhs; lhs;
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [display_z'', add_assoc_frm, x'', y'', z'']
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  -- Transform precondition of step of induction
  conv at ind =>
    rhs; lhs; intro; lhs
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [display_z'', add_assoc_frm, x'', y'', z'']
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  -- Transform postcondition of step of induction
  conv at ind =>
    rhs; lhs; intro; rhs
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [display_z'', add_assoc_frm, x'', y'', z'']
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  -- Transform the target of induction
  conv at ind =>
    rhs; rhs
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [display_z'', add_assoc_frm, x'', y'', z'']
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  -- Transform the actual target
  simp only [iAllsFv3, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
  repeat intro
  simp only [add_assoc_frm, x'', y'', z'']
  simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
  simp [Fin.snoc]

  -- Transform axioms
  have b3 := M.B3
  conv at b3 =>
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [B3_ax, x]
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  have b4 := M.B4
  conv at b4 =>
    simp only [iAllsFv2, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [B4_ax]
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
    simp [Fin.snoc]

  have b2 := M.B2
  conv at b2 =>
    simp only [iAllsFv2, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    repeat intro
    simp only [B2_ax, x]
    simp only [BoundedFormula.realize_relabel, HAdd.hAdd, Add.add, instHAdd]
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
    -- Option 1 (suggested by apply?):
    apply congrFun (congrArg HAdd.hAdd (hInd x y)) 1
    -- Option 2, more intuitively
    -- -- Auxiliary lemma (B2 in reverse) : x = y -> x + 1 = y + 1
    -- have b2_rev : forall (x y : M.num), x = y -> x + 1 = y + 1 := by {
    --   intro x' y' h
    --   rw [h]
    -- }
    -- apply b2_rev
    -- apply hInd

structure IDelta0Model extends BASICModel where
  delta0_induction {a} {k}
    (phi : peano.Formula (DisplayedFV1 ⊕ a))
    (h : a ≃ Fin k) :
    phi.IsDelta0 -> (mkInductionSentence h phi).Realize num

-- Example 3.9 D2; note that we bound the ∃ quantifier here! otherwise it doesn't make sense
def ex3_9_d2_frm : peano.Formula DisplayedFV3 := (x'' + z'') =' y'' ⊔ ((y'' + z'') =' x'')
def ex3_9_d2_frm_ex := iBdExsUniqueFv1 (display_z''2 ex3_9_d2_frm) (fun _ => x' + y')

@[simp]
theorem Term.realize_equal {L : Language} {M} [L.Structure M] {α} {v : α -> M} (t₁ t₂ : L.Term α) :
    (Term.equal t₁ t₂).Realize v ↔ t₁.realize v = t₂.realize v := by
  exact Formula.realize_equal

@[simp]
theorem BoundedFormula.realize_equal' {L : Language} {M} [h: L.Structure M] {α} {v : α -> M} (t₁ t₂ : L.Term α) {xs} :
    BoundedFormula.Realize (Term.equal t₁ t₂) v xs ↔ t₁.realize v = t₂.realize v := by
  let h' := @Formula.realize_equal _ _ h _ t₁ t₂ v
  let h'' : xs = default := by
    funext x
    exfalso
    apply Fin.elim0
    exact x
  unfold Formula.Realize at h'
  rw [<- h''] at h'
  exact h'

theorem idelta0_ex3_9_d1 (M : IDelta0Model.{_, _, _, 0}) : ∀ x : M.num, x ≠ 0 -> (∃ y, y <= x ∧ x = y + 1) := by
  sorry

theorem idelta0_ex3_9_d2 (M : IDelta0Model.{_, _, _, 0}) : ∀ x y : M.num, ∃! z, (x + z = y) ⊔ (y + z = x) := by
  -- induction on x
  have ind := M.delta0_induction (display_x' ex3_9_d2_frm_ex) DisplayedFV1.equivFin1 (by
    sorry
  )

  unfold mkInductionSentence Formula.iAllsComputable at ind
  unfold Sentence.Realize Formula.Realize at ind
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp] at ind

  -- Transform base
  conv at ind =>
    lhs
    simp only [BoundedFormula.alls, DisplayedFV1.equivFin1, Fin.isValue, Equiv.coe_fn_mk,
      BoundedFormula.realize_subst, peano.realize_zero_to_zero, BoundedFormula.realize_all,
      Nat.succ_eq_add_one, Nat.reduceAdd, BoundedFormula.realize_relabel, Nat.add_zero,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, BoundedFormula.realize_display_x',
      Function.comp_apply, Sum.map_inr, Sum.elim_inr, Sum.map_inl, id_eq, Sum.elim_inl]
    intro
    simp only [BoundedFormula.realize_relabel, BoundedFormula.realize_display_x', ex3_9_d2_frm_ex, iBdExsUniqueFv1, Formula.iBdExsUniqueComputable, Formula.iExsComputable]
    simp only [BoundedFormula.exs, BoundedFormula.realize_ex]
    rhs; intro
    simp only [BoundedFormula.realize_relabel, BoundedFormula.realize_inf, BoundedFormula.realize_iInf]
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, BoundedFormula.alls, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all]
    conv =>
      left; left
      simp only [Formula.realize_iInfComputable]
      intro
      simp only [peano.instAddTerm, x', y', peano.realize_zero_to_zero, Nat.add_zero,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        DisplayedFV1.equivFin1, Fin.isValue, Equiv.coe_fn_mk, Function.comp_apply, Sum.map_inr,
        Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
        cast_eq, Sum.map_inl, id_eq, Sum.elim_inl, peano.realize_leq_to_leq', Term.realize_var,
        Term.realize_relabel, peano.realize_add_to_add]
    conv =>
      left; right
      simp only [BoundedFormula.realize_display_z''2, ex3_9_d2_frm, Formula.eq_BoundedFormula, peano.instAddTerm, x'', z'', y'',
        peano.realize_zero_to_zero, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
        Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, DisplayedFV1.equivFin1, Fin.isValue,
        Equiv.coe_fn_mk, Function.comp_apply, Sum.map_inr, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero,
        lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq, Sum.map_inl, id_eq, Sum.elim_inl,
        BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, peano.realize_add_to_add,
        Term.realize_var]
    conv =>
      right
      simp only [Formula.iAllsComputable, BoundedFormula.alls, DisplayedFV1.equivFin1, Fin.isValue,
        Equiv.coe_fn_mk, Formula.eq_BoundedFormula, Formula.iInfComputable, peano.instAddTerm, x',
        y', Formula.Finset.toListComputable, Equiv.coe_fn_symm_mk, List.ofFn_succ, List.ofFn_zero,
        List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, display_z''2, Nat.add_zero,
        BoundedFormula.castLE_rfl, BoundedFormula.relabel_imp, BoundedFormula.relabel_inf,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_relabel,
        BoundedFormula.realize_inf, BoundedFormula.realize_top, and_true]
      intro
      unfold Formula.relabel
      simp only [BoundedFormula.relabel_inf, Nat.add_zero, Fin.snoc, Nat.reduceAdd, Fin.isValue,
        Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq,
        BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
        Function.comp_id, Fin.natAdd_zero, peano.realize_leq_to_leq', Term.realize_var,
        Sum.elim_inl, Function.comp_apply, Sum.elim_inr, Sum.map_inr, Term.realize_relabel,
        peano.realize_add_to_add, Sum.map_inl, id_eq, BoundedFormula.realize_top, and_true, and_imp]
      rhs
      simp only [ex3_9_d2_frm, Formula.eq_BoundedFormula, peano.instAddTerm, x'', z'', y'',
        Fin.isValue, BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual,
        peano.realize_add_to_add, Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.map_inl,
        id_eq, Sum.elim_inr, Sum.map_inr, Fin.snoc, Nat.reduceAdd, Fin.val_eq_zero,
        lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq]
      rhs

      rw [BoundedFormula.realize_equal']
      simp only [Fin.isValue, Term.realize_var, Function.comp_apply, Sum.map_inr, Sum.elim_inr,
        Fin.snoc, Nat.reduceAdd, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
        cast_eq, Sum.map_inl, id_eq, Sum.elim_inl]

  -- Transform step
  conv at ind =>
    intro
    simp only [iAllsFv1, Formula.iAllsComputableEmpty, Nat.add_zero, DisplayedFV1.equivFin1,
      Fin.isValue, Equiv.coe_fn_mk, peano.instAddTerm, BoundedFormula.relabel_imp, BoundedFormula.alls]
    conv =>
      lhs
      simp only [BoundedFormula.realize_all]
      intro
      simp only [BoundedFormula.realize_imp]
      conv =>
        lhs
        simp only [BoundedFormula.realize_relabel, ex3_9_d2_frm_ex, ex3_9_d2_frm]
        simp only [Fin.isValue, iBdExsUniqueFv1, Formula.iBdExsUniqueComputable,
          Formula.iExsComputable, Nat.add_zero, DisplayedFV1.equivFin1, Equiv.coe_fn_mk,
          Formula.eq_BoundedFormula, Formula.iInfComputable, peano.instAddTerm, x', y',
          Formula.Finset.toListComputable, Equiv.coe_fn_symm_mk, List.ofFn_succ, List.ofFn_zero,
          List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, display_z''2, x'', z'', y'',
          BoundedFormula.relabel_sup, BoundedFormula.castLE_rfl, Formula.iAllsComputable,
          BoundedFormula.relabel_imp, BoundedFormula.relabel_inf, Nat.succ_eq_add_one,
          Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
          BoundedFormula.realize_all, BoundedFormula.realize_relabel,
          BoundedFormula.realize_display_x', Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq,
          Sum.map_inl, id_eq, Sum.elim_inl]
        intro
        unfold BoundedFormula.exs
        unfold BoundedFormula.exs
        simp [BoundedFormula.realize_ex]
        rhs; intro;
        simp only [Fin.snoc, Nat.reduceAdd, Fin.isValue, Fin.val_eq_zero, lt_self_iff_false,
          ↓reduceDIte, Fin.reduceLast, cast_eq]
        right;
        unfold BoundedFormula.alls
        unfold BoundedFormula.alls
        simp only [BoundedFormula.realize_all]
        intro
        simp only [BoundedFormula.realize_imp]
        conv =>
          left
          unfold Formula.relabel
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, BoundedFormula.relabel_inf,
            Nat.add_zero, BoundedFormula.relabel_sup, BoundedFormula.realize_inf,
            BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
            Fin.natAdd_zero, peano.realize_leq_to_leq', Term.realize_var, Sum.elim_inl,
            Function.comp_apply, Sum.elim_inr, Sum.map_inr, Fin.snoc, Fin.val_eq_zero,
            lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq, Term.realize_relabel,
            peano.realize_add_to_add, Sum.map_inl, id_eq, BoundedFormula.realize_top, and_true,
            BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual]
        conv =>
          right
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, BoundedFormula.realize_inf,
            BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
            Function.comp_id, BoundedFormula.realize_equal', Term.realize_var, Function.comp_apply,
            Sum.map_inr, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte,
            Fin.reduceLast, cast_eq, Sum.map_inl, id_eq, Sum.elim_inl, BoundedFormula.realize_top,
            and_true]
      conv =>
        rhs
        simp only [display_x', ex3_9_d2_frm_ex, ex3_9_d2_frm]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Nat.add_zero, iBdExsUniqueFv1,
          Formula.iBdExsUniqueComputable, Formula.iExsComputable, DisplayedFV1.equivFin1,
          Equiv.coe_fn_mk, Formula.eq_BoundedFormula, Formula.iInfComputable, peano.instAddTerm, x',
          y', Formula.Finset.toListComputable, Equiv.coe_fn_symm_mk, List.ofFn_succ, List.ofFn_zero,
          List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, display_z''2, x'', z'', y'',
          BoundedFormula.relabel_sup, BoundedFormula.castLE_rfl, Formula.iAllsComputable,
          BoundedFormula.relabel_imp, BoundedFormula.relabel_inf, BoundedFormula.realize_relabel,
          Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, BoundedFormula.realize_subst,
          peano.realize_add_to_add, Term.realize_var, Function.comp_apply, Sum.elim_inr,
          peano.realize_one_to_one, BoundedFormula.realize_all, Fin.natAdd_zero]
        intro
        unfold BoundedFormula.exs BoundedFormula.alls
        unfold BoundedFormula.exs BoundedFormula.alls
        simp only [BoundedFormula.realize_ex]
        rhs; intro
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, BoundedFormula.relabel_all,
          Nat.add_eq, Nat.add_zero, BoundedFormula.relabel_imp, BoundedFormula.relabel_inf,
          Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq,
          BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Fin.castAdd_zero,
          Fin.cast_refl, Function.comp_id, peano.realize_leq_to_leq', Term.realize_var,
          Sum.elim_inl, Function.comp_apply, Sum.map_inr, Sum.elim_inr, Term.realize_relabel,
          peano.realize_add_to_add, Sum.map_inl, id_eq, BoundedFormula.realize_top, and_true,
          BoundedFormula.realize_sup, Fin.natAdd_zero, BoundedFormula.realize_bdEqual,
          BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_equal',
          Fin.natAdd_eq_addNat, Fin.addNat_one, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod,
          Nat.mod_succ, Fin.reduceNatAdd, Fin.reduceCastAdd, Nat.zero_mod, zero_lt_one,
          Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, Fin.castLT_eq_castPred,
          Fin.castPred_zero, Fin.castSucc_zero]
        right
        intro
        unfold Formula.relabel
        simp only [BoundedFormula.relabel_inf, Nat.add_zero, BoundedFormula.relabel_sup,
          Fin.isValue, BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Fin.castAdd_zero,
          Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, peano.realize_leq_to_leq',
          Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.elim_inr, Sum.map_inr, Fin.snoc,
          Nat.reduceAdd, Fin.natAdd_eq_addNat, Fin.addNat_one, Fin.succ_zero_eq_one,
          Fin.coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
          Fin.reduceNatAdd, cast_eq, Term.realize_relabel, peano.realize_add_to_add, Sum.map_inl,
          id_eq, Fin.val_eq_zero, BoundedFormula.realize_top, and_true, BoundedFormula.realize_sup,
          BoundedFormula.realize_bdEqual, and_imp]

  -- Transform goal of induction
  conv at ind =>
    intro; intro
    simp only [BoundedFormula.realize_all]
    intro
    simp only [display_x', ex3_9_d2_frm_ex, ex3_9_d2_frm]
    simp only [BoundedFormula.realize_relabel, BoundedFormula.realize_all, display_z''2]
    intro
    simp only [Nat.add_zero, iBdExsUniqueFv1, Formula.iBdExsUniqueComputable,
      Formula.iExsComputable, DisplayedFV1.equivFin1, Fin.isValue, Equiv.coe_fn_mk,
      Formula.eq_BoundedFormula, Formula.iInfComputable, peano.instAddTerm, x', y',
      Formula.Finset.toListComputable, Equiv.coe_fn_symm_mk, List.ofFn_succ, List.ofFn_zero,
      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, x'', z'', y'',
      BoundedFormula.relabel_sup, BoundedFormula.castLE_rfl, Formula.iAllsComputable,
      BoundedFormula.relabel_imp, BoundedFormula.relabel_inf, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, BoundedFormula.realize_relabel,
      Fin.natAdd_zero]
    unfold BoundedFormula.exs BoundedFormula.alls
    unfold BoundedFormula.exs BoundedFormula.alls
    simp only [BoundedFormula.realize_ex]
    rhs; intro;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, BoundedFormula.relabel_all,
      Nat.add_eq, Nat.add_zero, BoundedFormula.relabel_imp, BoundedFormula.relabel_inf,
      BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
      Function.comp_id, peano.realize_leq_to_leq', Term.realize_var, Sum.elim_inl,
      Function.comp_apply, Sum.map_inr, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false,
      ↓reduceDIte, Fin.reduceLast, cast_eq, Term.realize_relabel, peano.realize_add_to_add,
      Sum.map_inl, id_eq, BoundedFormula.realize_top, and_true, BoundedFormula.realize_sup,
      Fin.natAdd_zero, BoundedFormula.realize_bdEqual, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, BoundedFormula.realize_equal', Fin.natAdd_eq_addNat,
      Fin.addNat_one, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Fin.reduceNatAdd,
      Fin.reduceCastAdd, Nat.zero_mod, zero_lt_one, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, Fin.castLT_eq_castPred, Fin.castPred_zero, Fin.castSucc_zero]
    right; intro;
    unfold Formula.relabel
    simp only [BoundedFormula.relabel_inf, Nat.add_zero, BoundedFormula.relabel_sup, Fin.isValue,
      BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
      Function.comp_id, Fin.natAdd_zero, peano.realize_leq_to_leq', Term.realize_var, Sum.elim_inl,
      Function.comp_apply, Sum.elim_inr, Sum.map_inr, Fin.snoc, Nat.reduceAdd, Fin.natAdd_eq_addNat,
      Fin.addNat_one, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
      ↓reduceDIte, Fin.reduceLast, Fin.reduceNatAdd, cast_eq, Term.realize_relabel,
      peano.realize_add_to_add, Sum.map_inl, id_eq, Fin.val_eq_zero, BoundedFormula.realize_top,
      and_true, BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, and_imp]

  simp only [sup_Prop_eq]
  intro x y
  specialize ind ?_ ?_ x y
  -- base case: B2, O2
  · intro a
    exists a
    constructor
    · constructor
      · intro b
        -- a <= a + 0. easy!
        sorry
      · right
        -- 0 + a = a. easy!
        sorry
    · intro c hc hd
      cases hd with
      | inl hp =>
        -- a + c = 0, prove c = a. easy!
        sorry
      | inr hq =>
        -- 0 + c = a, prove c = a. easy!
        sorry
  -- induction step: B3, B4, D1
  · intro a hInd b
    cases hInd b with
    | intro w h =>
      have prevRes := h.left.right
      cases prevRes with
      | inl hp =>
        exists (w + 1)
        constructor
        · constructor
          · rw [<- hp]
            -- w <= b + b + w
            sorry
          · left
            rw [<- hp]
            sorry
        · intro cand2 hCandSmall hCandRes
          rw [<- hp] at hCandRes
          sorry
      | inr hq =>
        by_cases is_w_w : w = 0
        · exists 1
          constructor
          · constructor
            · sorry
            · left; sorry
          · intro cand hCandSmall hCandRes
            rw [is_w_w] at hq
            have hq' : a = b := by
              rw [<- hq]
              sorry
            rw [hq'] at hCandRes
            cases hCandRes with
            | inl hCandResL => sorry
            | inr HCandResR =>
              exfalso
              sorry
        · obtain ⟨pred, ⟨hpred1, hpred2⟩⟩ := idelta0_ex3_9_d1 M w is_w_w
          exists pred
          constructor
          · constructor
            · have h_PredSmall := h.left.left
              rw [hpred2] at h_PredSmall
              sorry
            · right
              -- use a + w = b, w = pred + 1
              sorry
          · intro cand hCandSmall hCandRes
            cases hCandRes with
            | inl hCandResL =>
              rw [<- hq] at hCandResL
              rw [hpred2] at hCandResL
              sorry
            | inr hCandResR =>
              rw [<- hq] at hCandResR
              rw [hpred2] at hCandResR
              sorry

  obtain ⟨indRes, indH⟩ := ind
  exists indRes
  constructor
  · simp
    exact indH.left.right.symm
  · intro candidate2
    simp
    intro candH
    have candH_small : candidate2 <= y + x := by
      sorry
    apply indH.right candidate2 candH_small
    exact candH.symm


-- Limited subtraction: The function x -' y := max(0, x - y) is Delta0-definable in IDelta0
-- First, define the relation by the defining axiom
def limited_subtraction_graph : peano.Formula DisplayedFV3 :=
  ((y'' + z'') =' x'') ⊔ (x'' <=' y'' ⊓ z'' =' 0)


-- Section 3.3.3 Defining y=2^x and BIT(i, x) in IDelta0 (Draft; p.53 of draft, p.64 of pdf)

-- Example 5.44 (The Pairing Function). We define the pairing function
-- ⟨x, y⟩ as the following term of IΔ₀:

-- Exercise 5.45 Show using the results in Section 3.1 that IΔ₀ proves ⟨x, y⟩
-- is a one-one function. That is

-- theorem idelta0_pair_one_one (M : IDelta0Model) : forall x1 x2 y1 y2, ⟨x1, y1⟩ = ⟨x2, y2⟩ -> (x1 = x2 ∧ y1 = y2) := by
--   sorry
-- -- (First show that the LHS implies x₁ + y₁ = x₂ + y₂)
