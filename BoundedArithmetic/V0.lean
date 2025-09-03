-- This file demonstrates how we can encode the two-sorted logic used for V^0
-- in single-sorted logic modeled by Mathlib.ModelTheory
-- We use the idea described in section 4.5 Single-sorted logic interpretation
-- (Draft p.82 = p.93 of pdf) (draft: https://www.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf)

-- NOTE: this file is older and while working on it, I wasn't sure how to properly work with
-- free variables in formulas for induction / comprehension:
-- - how to display one particular variable to be bound by the induction scheme
-- - how to bypass 'bounded' (in mathlib's vocab) variables not being quantifiable over in the ModelTheory library
-- I have better solutions for these problems in the IDelta0.lean file,
-- these files for now contain the old, bad design
-- in particular, the way I deal with de Bruijn indices in this file is super brittle

import BoundedArithmetic.BoundedModelTheory.Basic
import BoundedArithmetic.BoundedModelTheory.Syntax
import BoundedArithmetic.BoundedModelTheory.Complexity
import Mathlib.Tactic.Linarith

namespace FirstOrder

-- to represent the language, we use this idea from July 22 2025:
-- https://github.com/leanprover-community/mathlib4/blob/909b3bebf314f6bcdb73d82d2a14f3f38a5bb5da/Mathlib/ModelTheory/Arithmetic/Presburger/Basic.lean#L30-L35

-- Definition 4.4, Draft page 70 (page 81 of pdf)
-- + note about adding the axiom "E" and empty-string constant in a section below
inductive V0Func : Nat -> Type
| zero : V0Func 0
| one : V0Func 0
| empty : V0Func 0
| len : V0Func 1
| add : V0Func 2
| mul : V0Func 2
deriving DecidableEq

inductive V0Rel : Nat -> Type
-- | eqsort, eqstr -- we will use built-in equality syntax from ModelTheory lib
| isnum : V0Rel 1
| isstr : V0Rel 1
| leq : V0Rel 2
| mem : V0Rel 2
deriving DecidableEq

def Lang : FirstOrder.Language :=
{ Functions := V0Func,
  Relations := V0Rel
}

-- Cook, Nguyen: introduction, Draft page 5 of pdf:
-- Most of the theories presented in this book, including those in (2), have the
-- same “second-order” underlying language L2A, introduced by Zambella. The
-- language L2 A is actually a language for the two-sorted first-order predicate cal-
-- culus, where one sort is for sortbers in N and the second sort is for finite sets of
-- sortbers. Here we regard an object of the second sort as a finite string over the
-- alphabet {0, 1} (the i-th bit in the string is 1 iff i is in the set). The strings are
-- the objects of interest for the complexity classes, and serve as the main inputs
-- for the machines or circuits that determine the class. The sortbers serve a use-
-- ful purpose as indices for the strings when describing properties of the strings.
-- When they are used as machine or circuit inputs, they are presented in unary
-- notation.
namespace Language.zambella

@[simp] def isOpen {a} {n} [DecidableEq a] (formula : Lang.BoundedFormula a n) := FirstOrder.Language.BoundedFormula.IsQF formula

@[simp] def contains_var_zero {a} [DecidableEq a] {n} (t : Lang.Term (a ⊕ Fin n)) : Bool :=
  if h_eq : n = 0 then
    false
  else
    (Sum.inr $ @Fin.mk n 0 (Nat.pos_of_ne_zero h_eq)) ∈ t.varFinset

@[simp] def relationLeq : Lang.Relations 2 := V0Rel.leq
@[simp] def relationMem : Lang.Relations 2 := V0Rel.mem
@[simp] def relationIsnum : Lang.Relations 1 := V0Rel.isnum

-- --- Sentence Construction Helpers ---
-- For sentences, α is Empty, and n is 0.

-- A variable term (for current context `n`).
-- For sentences, `n = 0`, so `Fin 0` is `Empty`.
-- If we're inside `all {n} f`, then `f` has context `n+1`, so `Fin (n+1)`.
@[simp] def var_term {k : ℕ} (idx : Fin k) : Term Lang (Empty ⊕ (Fin k)) := Term.var (Sum.inr idx)

-- A constant term. Now `k` is a free variable, so Lean can infer it.
-- This term type is `Term Lang (α ⊕ (Fin k))`
@[simp] def const_term {α} {k : ℕ} (c : Lang.Functions 0) : Term Lang (α ⊕ (Fin k)) := Term.func c ![]

-- A term from a binary function (e.g., add, mul). `k` is also generic here.
@[simp] def binary_func_term {α} {k : ℕ} (f : Lang.Functions 2) (t1 t2 : Term Lang (α ⊕ (Fin k))) : Term Lang (α ⊕ (Fin k)) := Term.func f ![t1, t2]

@[simp] def not_form {a} {k : ℕ} (f : BoundedFormula Lang a k) : BoundedFormula Lang a k :=
  BoundedFormula.not f

@[simp] def isnum_form {k : ℕ} (t1 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationIsnum ![t1]

-- Atomic formulas
@[simp] def eq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.equal t1 t2

@[simp] def leq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationLeq ![t1, t2]

@[simp] def mem_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationMem ![t1, t2]

@[simp] def falsum_form {a} {k : ℕ} : Lang.BoundedFormula a k := BoundedFormula.falsum

@[simp] def and_form {a} {k : ℕ} (f1 f2 : BoundedFormula Lang a k) : BoundedFormula Lang a k :=
  max f1 f2

@[simp] def imp_form {a} {k : ℕ} (f1 f2 : BoundedFormula Lang a k) : BoundedFormula Lang a k :=
  BoundedFormula.imp f1 f2

@[simp] def ex_form {a} {k : ℕ} (f : BoundedFormula Lang a (k + 1)) : BoundedFormula Lang a k :=
  BoundedFormula.ex f

@[simp] def all_form {a} {k : ℕ} (f : BoundedFormula Lang a (k + 1)) : BoundedFormula Lang a k :=
  BoundedFormula.all f

-- Section 3.1 Peano Arithmetic (Draft, page 34 (45 of pdf))

structure TwoSortedBASICModel where
  sort    : Type

  -- Functions and predicates for sort
  zero   : sort
  one    : sort
  empty  : sort
  add    : sort → sort → sort
  mul    : sort → sort → sort
  len    : sort -> sort
  isnum  : sort -> Prop
  isstr  : sort -> Prop
  leq    : sort → sort → Prop
  mem    : sort -> sort -> Prop
  -- we want to be able to reason by contradiction
  [leq_dec : DecidableRel leq]
  [mem_dec : DecidableRel mem]

  -- typing axioms; 4.5 Single-sorted logic interpretation (Draft p.83 / p.94 of pdf)
  TypeDec   : ∀ x, isnum x ∨ isstr x
  TypeZero  : isnum zero
  TypeOne   : isnum one
  TypeEmpty : isstr empty
  TypeAdd   : forall x y, isnum x -> isnum y -> isnum (add x y)
  TypeMul   : forall x y, isnum x -> isnum y -> isnum (mul x y)
  TypeLen   : forall x, isstr x -> isnum (len x)
  TypeLeq   : forall x y, leq x y -> (isnum x ∧ isnum y)
  TypeMem   : forall x y, mem x y -> (isnum x ∧ isstr y)

  -- axiom for empty string; 4.4.1 Two-Sorted Free Variable Normal Form
  E : len empty = zero

  -- B1. x + 1 ≠ 0
  B1 : ∀ (x : sort), isnum x -> add x one ≠ zero
  -- B2. x + 1 = y + 1 ⊃ x = y
  B2 : ∀ (x y : sort), isnum x -> isnum y -> add x one = add y one → x = y
  -- B3. x + 0 = x
  B3 : ∀ (x : sort), isnum x -> add x zero = x
  -- B4. x + (y + 1) = (x + y) + 1
  B4 : ∀ (x y : sort), isnum x -> isnum y -> add x (add y one) = add (add x y) one
  -- B5. x · 0 = 0
  B5 : ∀ (x : sort), isnum x -> mul x zero = zero
  -- B6. x · (y + 1) = (x · y) + x
  B6 : ∀ (x y : sort), isnum x -> isnum y -> mul x (add y one) = add (mul x y) x
  -- B7. (x ≤ y ∧ y ≤ x) ⊃ x = y
  B7 : ∀ (x y : sort), isnum x -> isnum y -> leq x y → leq y x → x = y
  -- B8. x ≤ x + y
  B8 : ∀ (x y : sort), isnum x -> isnum y -> leq x (add x y)
  B9 : ∀ (x : sort), isnum x -> leq zero x
  B10 : forall x y : sort, isnum x -> isnum y -> leq x y ∨ leq y x
  B11 : forall x y : sort, isnum x -> isnum y -> leq x y ↔ (leq x (add y one) ∧ x ≠ (add y one))
  B12 : forall x : sort, isnum x -> x ≠ zero -> (∃ y : sort, (leq y x ∧ (add y one) = x))
  L1 : forall X y : sort, isstr X -> isnum y -> mem y X -> (leq y (len X) ∧ y ≠ (len X))
  L2 : forall X y : sort, isstr X -> isnum y -> (add y one) = len X -> mem y X

  SE : forall X Y : sort,
    isstr X ->
    isstr Y ->
    len X = len Y ->
    (forall i : sort,
      ((leq i (len X) ∧ i ≠ (len X)) ->
        mem i X ↔ mem i Y
      )
    ) ->
    X = Y

instance TwoSortedBASICModel_Structure (M : TwoSortedBASICModel) : Lang.Structure M.sort :=
{
  -- Carrier := fun _ => M.sort,
  funMap := fun {arity} f =>
    match arity, f with
    | 0, V0Func.zero => fun _ => M.zero
    | 0, V0Func.one => fun _ => M.one
    | 0, V0Func.empty => fun _ => M.empty
    | 1, V0Func.len => fun args => M.len (args 0)
    | 2, V0Func.add => fun args => M.add (args 0) (args 1)
    | 2, V0Func.mul => fun args => M.mul (args 0) (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    | 1, V0Rel.isnum => fun args => M.isnum (args 0)
    | 1, V0Rel.isstr=> fun args => M.isnum (args 0)
    | 2, V0Rel.leq => fun args => M.leq (args 0) (args 1)
    | 2, V0Rel.mem => fun args => M.mem (args 0) (args 1)
}

@[simp] def realize_at : forall {n}, (M : TwoSortedBASICModel) -> Lang.BoundedFormula Empty (n + 1) -> M.sort -> Prop
| 0, M, phi, term => @phi.Realize Lang M.sort (TwoSortedBASICModel_Structure M) _ _ (Empty.elim) ![term]
| _ + 1, M, phi, term => realize_at M phi.all term

-- TODO: DEBRUIJN: here I assumed 0 deBruijn index is the closest quantifier. but this does not seem to be right!
-- for now, I changed 0 to n
inductive IsSigma0B : {n : Nat} -> Lang.BoundedFormula Empty n -> Prop
| of_isQF {phi} (h : BoundedFormula.IsQF phi) : IsSigma0B phi
-- bounded number quantifiers are allowed
| bdNumEx  {n} {phi : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi):  IsSigma0B $ ex_form $ and_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)
| bdNumAll {n} {phi : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi) : IsSigma0B $ all_form $ imp_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)
-- enable optional type implication
| bdNumAll' {n} {phi : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi) : IsSigma0B $ all_form $ imp_form (isnum_form (var_term (Fin.ofNat (n + 1) n))) $ imp_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)

def TwoSortedBASICModel.lt (M : TwoSortedBASICModel) (x y : M.sort) : Prop :=
  M.leq x y ∧ x ≠ y

-- p. 87 Draft (98 of pdf)
structure V0Model extends TwoSortedBASICModel where
  sigma0B_comp {n} :
    ∀ (phi_syntax : Lang.BoundedFormula Empty (n + 1)),
    IsSigma0B phi_syntax ->
    -- X must not occur free in phi(z); 1 is deBruijn index for second-shallowest quantifier
    -- no_free 1 phi_syntax ->
    -- ∀ y ∃ X <= y ∀ z < y, (z ∈ X ↔ φ(z))
    forall n_free_vars : Fin (n - 2) -> sort,
    (
    forall y : sort,
      isnum y ->
      (∃ X : sort, isstr X ∧ leq (len X) y ∧
        (∀ z : sort,
          isnum z ->
          ((leq z y ∧ z ≠ y) ->
            (
              mem z X ↔
              @phi_syntax.Realize
                Lang
                sort
                (TwoSortedBASICModel_Structure toTwoSortedBASICModel)
                _ _ (Empty.elim)
                (fun (idx : Fin (n + 1)) =>
                  let free_vars := List.ofFn n_free_vars ++ [z, X, y]
                  -- let free_vars := [z, X, y] ++ List.ofFn n_free_vars
                  have h2 : (n + 1) <= free_vars.length := by
                    unfold free_vars
                    simp
                    match n with
                    | 0 => simp
                    | 1 => simp
                    | k + 2 => simp
                  have idx_cast : Fin free_vars.length := Fin.castLE h2 idx
                  List.get free_vars idx_cast
                )
          )
        )
      )
    )
    )

instance V0Model_Structure (M : V0Model) : Lang.Structure M.sort :=
{
  funMap := fun {arity} f =>
    match arity, f with
    | 0, V0Func.zero => fun _ => M.zero
    | 0, V0Func.one => fun _ => M.one
    | 0, V0Func.empty => fun _ => M.empty
    | 1, V0Func.len => fun args => M.len (args 0)
    | 2, V0Func.add => fun args => M.add (args 0) (args 1)
    | 2, V0Func.mul => fun args => M.mul (args 0) (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    | 1, V0Rel.isnum => fun args => M.isnum (args 0)
    | 1, V0Rel.isstr => fun args => M.isstr (args 0)
    | 2, V0Rel.leq => fun args => M.leq (args 0) (args 1)
    | 2, V0Rel.mem => fun args => M.mem (args 0) (args 1)
}

-- Lemma 5.6 (p. 87 Draft / 98 of pdf); V^0 ⊢ X-MIN

-- phi(z) := forall y' <= z, ¬X(y')
-- the final comprehension axiom acquired will go:
-- forall y, exists Y <= y, forall z < |X|, mem z Y ↔ (forall y' <= z, ¬X(y'))
-- beware of the name collision
-- (y comes from universalization of comp axiom, y' used only inside phi)
def v0_xmin_comp1_form :=
  -- now we're inside of the 'phi' above
  let y' := var_term (4 : Fin 5)
  let z := var_term (1 : Fin 5)
  let X := var_term (0 : Fin 5)
  all_form $ imp_form (isnum_form y') $ imp_form (leq_form y' z) (not_form $ mem_form y' X)

def v0_xmin_comp1_form_shallow (M : V0Model) :=
  ∀ X, M.isstr X -> (
    ∀y,
      ∃ Y,
        (M.leq (M.len Y) y) ∧
        (∀ z,
          M.isnum z ->
          (M.lt z (M.len Y)) ->
          (∀ y', (M.leq y' z) -> ¬M.mem y' X
          )
        )
  )

def v0_xmin_form_shallow (M : V0Model) : Prop :=
  forall X,
    M.isstr X ->
    M.lt M.zero (M.len X) ->
    exists x,
      (
        M.lt x (M.len X) ∧
        M.mem x X ∧
        (forall y, M.isnum y -> M.lt y x -> ¬ M.mem y X)
      )

theorem v0_xmin (M : V0Model) : v0_xmin_form_shallow M := by
  -- by Sigma0B-COMP, there is a set Y such that |Y| <= |X| and for all z < |X|,
  -- Y(z) <-> $ Forall y, y <= z -> not X(y)
  have h_comp := M.sigma0B_comp v0_xmin_comp1_form
  have h_comp' := h_comp (by
    unfold v0_xmin_comp1_form
    apply IsSigma0B.bdNumAll'
    apply IsSigma0B.of_isQF
    apply BoundedFormula.IsQF.imp
    apply BoundedFormula.IsQF.of_isAtomic
    apply BoundedFormula.IsAtomic.rel
    apply BoundedFormula.IsQF.falsum
  )
  clear h_comp
  intro X h_X_type h_X_len_pos
  have h_comp'' := h_comp' ![X] (M.len X)
  clear h_comp'
  have h_comp3 := h_comp'' (by
    apply M.TypeLen
    exact h_X_type
  )
  clear h_comp''
  -- now, the Y we obtain is exactly the Y from the proof!
  obtain ⟨Y, h_Y_type, h_Y_len, h_Y_content⟩ := h_comp3
  unfold v0_xmin_comp1_form at h_Y_content
  simp at h_Y_content
  simp [BoundedFormula.Realize] at h_Y_content
  simp [FirstOrder.Language.Structure.RelMap] at h_Y_content
  simp [Fin.snoc] at h_Y_content

  -- [...] Thus the set Y consists of the numbers smaller than every element in X.
  -- Assuming 0 < |X| [h_X_len_pos], we will show that |Y| is the least member of X.
  -- Intuitively, this is because |Y| is the least number that is larger than
  -- any member of Y. Formally, we need to show:
  -- (i) X(|Y|)
  -- (ii) ∀ y < |Y|, ¬X(y)
  -- Details are as follows.
  have h_i_ii : M.mem (M.len Y) X ∧ (∀ t, M.isnum t -> M.lt t (M.len Y) -> ¬ M.mem t X) := by
  -- First, suppose that Y is empty.
    if h_Y_empty : Y = M.empty then {
      refine ⟨?_, ?_⟩
      rw [h_Y_empty]
      rw [M.E]
      by_contra h_zero_not_mem_X
      -- prove (i) X(|Y|)
      · -- from definition of Y, having the assumption (contradictory) that
        -- zero is not in X, try to obtain element of Y. since Y empty, contr.
        specialize h_Y_content M.zero M.TypeZero ?_ ?_
        -- prove 0 <= |X|
        · unfold TwoSortedBASICModel.lt at h_X_len_pos
          obtain ⟨h_X_len_leq_zero, _ ⟩ := h_X_len_pos
          apply (h_X_len_leq_zero)
        -- prove 0 ≠ |X|
        · unfold TwoSortedBASICModel.lt at h_X_len_pos
          obtain ⟨_, h_X_len_neq_zero⟩ := h_X_len_pos
          apply (h_X_len_neq_zero)
        -- now in h_Y_content we should have something of the form:
        -- forall a, isnum a -> leq a 0 -> ¬ mem a X
        have Yc' := (Iff.mpr h_Y_content)
        have h_zero_not_mem_Y : ¬ M.mem M.zero Y := by
          intro h_zero_mem_Y
          have ⟨_, h_zero_neq_len_Y⟩ := M.L1 Y M.zero h_Y_type M.TypeZero h_zero_mem_Y
          apply h_zero_neq_len_Y
          rw [h_Y_empty]
          rw [M.E]
        apply h_zero_not_mem_Y
        apply Yc'
        intro a h_a_type h_a_leq_zero h_a_mem_X
        apply h_zero_not_mem_X
        -- now, prove that a = 0
        have h_a_eq_zero : a = M.zero := by
          apply M.B7 a M.zero h_a_type M.TypeZero
          · exact h_a_leq_zero
          · apply M.B9 a h_a_type
        rw [h_a_eq_zero] at h_a_mem_X
        exact h_a_mem_X
      -- prove (ii) ∀ y < |Y|, ¬X(y)
      · intro t h_t_type h_t_lt_len_Y h_t_mem_X
        rw [h_Y_empty] at h_t_lt_len_Y
        rw [M.E] at h_t_lt_len_Y
        obtain ⟨h_t_leq_zero, h_t_neq_zero⟩ := h_t_lt_len_Y
        apply h_t_neq_zero
        apply M.B7 t M.zero h_t_type M.TypeZero
        apply h_t_leq_zero
        apply M.B9 t h_t_type
    } else {
      -- Now suppose that Y is not empty, i.e. Y(y) holds for some y.
      -- ...
      sorry
    }

  -- now, finish the proof!
  have ⟨h_len_Y_mem_X, h_len_Y_is_min⟩ := h_i_ii
  clear h_i_ii

  exists (M.len Y)
  refine ⟨?_, ?_, ?_⟩
  · apply M.L1 X (M.len Y) h_X_type (M.TypeLen Y h_Y_type) h_len_Y_mem_X
  · apply h_len_Y_mem_X
  · apply h_len_Y_is_min
