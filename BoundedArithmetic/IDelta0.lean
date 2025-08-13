import Lean
import BoundedArithmetic.BoundedModelTheory.Basic
import BoundedArithmetic.BoundedModelTheory.Syntax
import BoundedArithmetic.BoundedModelTheory.Complexity
import BoundedArithmetic.BoundedModelTheory.Semantics

open Lean Elab Term Meta Syntax

universe u
variable (a : Type u)

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
inductive PeanoFunc : Nat -> Type
  | zero : PeanoFunc 0
  | one : PeanoFunc 0
  | add : PeanoFunc 2
  | mul : PeanoFunc 2
  deriving DecidableEq

inductive PeanoRel : Nat -> Type
  | leq : PeanoRel 2
  deriving DecidableEq

def Language.peano : Language :=
{ Functions := PeanoFunc,
  Relations := PeanoRel
}

namespace Language

namespace Formula
/-- Computable version of FirstOrder.Language.Formula.iAlls -/
def iAllsComputable {L : Language} {α β} {k} (e : β ≃ Fin k) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

def iAllsComputableEmpty {L : Language} {β} {k} (e : β ≃ Fin k) (φ : L.Formula β) : L.Formula Empty :=
  (BoundedFormula.relabel (fun a => Sum.inr $ e a) φ).alls
end Formula

namespace peano

instance : Zero (peano.Term a) where
  zero := Constants.term .zero

instance : One (peano.Term a) where
  one := Constants.term .one

instance : Add (peano.Term a) where
  add := Functions.apply₂ .add

instance : Mul (peano.Term a) where
  mul := Functions.apply₂ .mul

instance : SMul ℕ (peano.Term a) where
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
def Term.bdNeq {a} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  ∼(t1 =' t2)

/-- The less-than-or-equal relation of two terms as a bounded formula -/
def Term.bdLeq {a} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  Relations.boundedFormula₂ FirstOrder.PeanoRel.leq t1 t2

-- inspired by https://github.com/leanprover-community/mathlib4/blob/cff2a6ea669abe2e384ea4c359f20ee90a5dc855/Mathlib/ModelTheory/Syntax.lean#L732
@[inherit_doc] scoped[FirstOrder] infixl:88 " ≠' " => Language.peano.Term.bdNeq
@[inherit_doc] scoped[FirstOrder] infixl:88 " <=' " => Language.peano.Term.bdLeq

/-- The less-than relation of two terms as a bounded formula -/
def Term.bdLt {a} {n} (t1 t2 : peano.Term (a ⊕ (Fin n))) : peano.BoundedFormula a n :=
  (t1 <=' t2) ⊓ ∼(t1 =' t2)

@[inherit_doc] scoped[FirstOrder] infixl:88 " <' " => Language.peano.Term.bdLt


-- declare_syntax_cat logic_expr
-- scoped syntax ident : logic_expr
-- scoped syntax logic_expr " -> " logic_expr : logic_expr
-- scoped syntax "(" logic_expr ")" : logic_expr
-- scoped syntax "[Peano| " logic_expr "]" : term


-- scoped elab_rules : term
--   | `([Logic| $e:logic_expr]) => elabTerm e none
--   | `(logic_expr| $i:ident) => do
--       let nameExpr ← Term.elabTerm i none
--       return mkApp (mkConst ``Formula.var) nameExpr

--   | `(logic_expr| $p:logic_expr -> $q:logic_expr) => do
--       let lhs ← elabTerm (← `([Logic| $p])) none
--       let rhs ← elabTerm (← `([Logic| $q])) none
--       return mkApp2 (mkConst ``Formula.imp) lhs rhs

--   | `(logic_expr| ($p)) => do
--       elabTerm (← `([Logic| $p])) none

end peano

namespace BoundedFormula

/-- Notes about de Bruijn indices as used in Mathlib.ModelTheory
  Take a look at how is BoundedFormula.Realize implemented:
  `| _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)`

  Recall that  `Fin.snoc xs x` takes a tuple `xs : Fin n -> SomeType` and turns
  it into a tuple with `x` appended at the end,
  i.e. `xs' : Fin (n + 1) -> SomeType` with `n` mapped into `x`

  Now, how is BoundedFormula.relabel implemented?
  Not the way we want - we can only substitute a free var with a specific term,
  but the term has to be different, depending on the quantifier depth of
  the place where the free var occurs in the ofrmua

  But: Mathlib.ModelTheory offers us constantsVarsEquiv function!
  e.g. to move free vars into language constants: constantsVarsEquiv.symm phi.alls
--/

inductive DisplayedFV1 | x
inductive DisplayedFV2 | x | y
inductive DisplayedFV3 | x | y | z

-- this could easily be computable!! but Equiv.ofBijective is noncomputable!
noncomputable def DisplayedFV1EquivFin1 : (DisplayedFV1 ≃ Fin 1) :=
  Equiv.ofBijective
    (fun _ => 0)
    (by
      simp only [Function.Bijective, Function.Injective, Function.Surjective]
      constructor
      · intro _ _ h
        exact h
      · intro b
        apply Fin.eq_zero at b
        rw [b]
        exists DisplayedFV1.x
    )

-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
noncomputable def mkInductionSentence {n} {a} {k} (h : a ≃ Fin k) (phi: peano.BoundedFormula (DisplayedFV1 ⊕ a) n) :=
  (phi.alls.iAllsComputable h).iAllsComputableEmpty DisplayedFV1EquivFin1

-- Display a free variable in -/
inductive NameOrSpecial (T : Type u)
| standard (_ : T) : NameOrSpecial T
| special : NameOrSpecial T

/-- Helper to quantify over a free variable, which Mathlib.ModelTheory was not designed for -/
def existsSpecial {a} {L : FirstOrder.Language} (f : L.Formula (NameOrSpecial a)) : L.Formula a :=
  let relabel_fun {x} : NameOrSpecial a -> a ⊕ Fin (x + 1) :=
    fun fvName =>
      match fvName with
        | .standard a' => Sum.inl a'
        | .special => Sum.inr $ Fin.ofNat (x + 1) x
  let f_relabeled := f.mapTermRel
    (fun _ t => t.relabel (Sum.elim relabel_fun (Sum.inr ∘ Fin.castSucc))) -- ft
    (fun _ => id) -- fr
    (fun x => castLE (by rfl)) -- h
  ex f_relabeled


-- TA MASZYNERIA JEST NIEPOPRAWNA! formuła phi := `All.$0 neq 0` jest na level 0, ale
-- nie mozemy teraz na zrobić phi ⊓ psi, gdzie psi := `$0 neq $1` i skwantyfikować
-- na pałę `All.All. phi ⊓ psi`!
-- a może jest?

/-- Helper for building quantified formulas without messing up the de Bruijn binding -/
-- def namedEx {a} {n} {L : FirstOrder.Language} (f : L.BoundedFormula (NameOrSpecial a) n) : L.BoundedFormula a n :=
--   let relabel_fun {x} : NameOrSpecial a -> a ⊕ Fin (x + 1) :=
--     fun fvName =>
--       match fvName with
--         | .standard a' => Sum.inl a'
--         | .special => Sum.inr $ Fin.ofNat (x + 1) x
--   let f_relabeled := f.mapTermRel
--     (fun _ t => t.relabel (Sum.elim relabel_fun (Sum.inr ∘ Fin.castSucc))) -- ft
--     (fun _ => id) -- fr
--     (fun x => castLE (by rfl)) -- h
--   ex f_relabeled

-- def namedAll {a} {n} {L : FirstOrder.Language} (f : L.BoundedFormula (NameOrSpecial a) n) : L.BoundedFormula a n :=
--   let relabel_fun {x} : NameOrSpecial a -> a ⊕ Fin (x + 1) :=
--     fun fvName =>
--       match fvName with
--         | .standard a' => Sum.inl a'
--         -- if `phi` is at level `n + 1`, then `n` (highest index) is the deBruijn ind of `x`
--         | .special => Sum.inr $ Fin.ofNat (x + 1) x
--   let f_relabeled := f.mapTermRel
--     (fun _ t => t.relabel (Sum.elim relabel_fun (Sum.inr ∘ Fin.castSucc))) -- ft
--     (fun _ => id) -- fr
--     (fun x => castLE (by rfl)) -- h
--   all f_relabeled

-- Definition 3.7, page 36 of draft (47 of pdf)
abbrev isOpen {a} {n} [DecidableEq a] (formula : peano.BoundedFormula a n) := FirstOrder.Language.BoundedFormula.IsQF formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
inductive IsDelta0 {a} : {n : Nat} -> peano.BoundedFormula a n -> Prop
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
      (&(Fin.ofNat (n + 1) n))  -- lift `n` into Term.var; this denotes just `x`
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

def x := (var (Sum.inr 0) : peano.Term (Empty ⊕ Fin 1))

protected def B1_ax : peano.Sentence := ∀' (Term.func PeanoFunc.zero)  ≠' Constants.zero

class BASICModel {M : Type*} [h : peano.Structure M] where
  B1 : M ⊨ BoundedFormula.namedAll ((x + h.funMap) ≠' 0)

  -- B1 : ∀ (x : M), (x + 1) ≠' 0


-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
structure BASICModel where
  num : Type

  zero : num
  one : num
  add : num -> num -> num
  mul : num -> num -> num
  leq : num -> num -> Prop

  -- B1. x + 1 ≠ 0
  B1 : ∀ (x : num), add x one ≠ zero

  -- B2. x + 1 = y + 1 ⊃ x = y
  B2 : ∀ (x y : num), add x one = add y one -> x = y

  -- B3. x + 0 = x
  B3 : ∀ (x : num), add x zero = x

  -- B4. x + (y + 1) = (x + y) + 1
  B4 : ∀ (x y : num), add x (add y one) = add (add x y) one

  -- B5. x · 0 = 0
  B5 : ∀ (x : num), mul x zero = zero

  -- B6. x · (y + 1) = (x · y) + x
  B6 : ∀ (x y : num), mul x (add y one) = add (mul x y) x

  -- B7. (x ≤ y ∧ y ≤ x) ⊃ x = y
  B7 : ∀ (x y : num), leq x y -> leq y x -> x = y

  -- B8. x ≤ x + y
  B8 : ∀ (x y : num), leq x (add x y)

  -- C. 0 + 1 = 1
  C : add zero one = one


instance BASICModel_Structure (M : BASICModel) : peano.Structure M.num :=
{
  funMap := fun {arity} f =>
    match arity, f with
    | 0, .zero => fun _ => M.zero
    | 0, .one => fun _ => M.one
    | 2, .add => fun args => M.add (args 0) (args 1)
    | 2, .mul => fun args => M.mul (args 0) (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    | 2, .leq => fun args => M.leq (args 0) (args 1)
}

def realize_at : forall {n}, (M : BASICModel) -> peano.BoundedFormula Empty (n + 1) -> M.num -> Prop
| 0, M, phi, term => @phi.Realize peano M.num (BASICModel_Structure M) _ _ (Empty.elim) ![term]
| _ + 1, M, phi, term => realize_at M phi.all term

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)

)

structure IOPENModel extends BASICModel where
  open_induction {n} :
    ∀ (phi_syntax : peano.BoundedFormula Empty (n + 1)),
    BoundedFormula.isOpen phi_syntax ->
    -- phi(0)
    realize_at toBASICModel phi_syntax zero ->
    -- (∀ x : num, φ x -> φ (add x one)) ->
    (forall x : num,
      realize_at toBASICModel phi_syntax x ->
      realize_at toBASICModel phi_syntax (add x one)
    ) ->
    -- ∀ x, φ x
    (forall x : num, realize_at toBASICModel phi_syntax x)

-- Example 3.8 (draft) The following formulas (and their universal closures) are theorems of IOPEN:
-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z
def add_assoc_form :=
-- deBruijn indices
  let x := var_term (2 : Fin 3)
  let y := var_term (1 : Fin 3)
  let z := var_term (0 : Fin 3)
  let lhs := binary_func_term Functions2.add (binary_func_term Functions2.add x y) z
  let rhs := binary_func_term Functions2.add x (binary_func_term Functions2.add y z)
  eq_form lhs rhs

def add_assoc_form_shallow (M : IOPENModel) := ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)

def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]

theorem iopen_add_assoc_iff (M : IOPENModel) : add_assoc_form_shallow M <-> add_assoc_form_deep M := by {
  apply Iff.intro
  · intro h
    unfold add_assoc_form_deep
    unfold add_assoc_form
    simp [eq_form, binary_func_term, var_term]
    repeat unfold BoundedFormula.alls
    simp
    unfold add_assoc_form_shallow at h
    intros x y z
    specialize h z y x
    rw [<- Term.bdEqual]
    simp
    simp [FirstOrder.peanouage.Structure.funMap, Fin.snoc]
    exact h
  · intro h
    unfold add_assoc_form_shallow
    intros x y z
    unfold add_assoc_form_deep at h
    unfold add_assoc_form at h
    simp [eq_form, binary_func_term, var_term] at h
    repeat unfold BoundedFormula.alls at h
    simp at h
    specialize h z y x
    rw [<- Term.bdEqual] at h
    simp at h
    simp [FirstOrder.peanouage.Structure.funMap, Fin.snoc] at h
    exact h
}

theorem iopen_add_assoc (M : IOPENModel) : ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z) := by {
  rw [<- add_assoc_form_shallow]
  rw [iopen_add_assoc_iff]
  apply M.open_induction add_assoc_form
  -- prove that add_assoc_form is OPEN
  · unfold add_assoc_form
    apply BoundedFormula.IsQF.of_isAtomic
    apply BoundedFormula.IsAtomic.equal
  -- prove phi(0)
  · unfold add_assoc_form
    simp [realize_at]
    unfold eq_form
    intros a b
    simp [BoundedFormula.Realize, binary_func_term, var_term]
    simp [FirstOrder.peanouage.Structure.funMap, Fin.snoc]
    -- use B3. x + 0 = x
    rw [M.B3 (M.add b a)]
    rw [M.B3 a]
  -- prove that forall x, (phi(x) -> phi(x + 1))
  · intros x ih
    unfold add_assoc_form
    simp [realize_at]
    intros y z
    simp [BoundedFormula.Realize, eq_form, binary_func_term, var_term]
    simp [FirstOrder.peanouage.Structure.funMap, Fin.snoc]
    -- use B4. x + (y + 1) = (x + y) + 1
    repeat rw [M.B4]
    -- try to use B2 in reverse: x + 1 = y + 1 <- x = y
    have b2_rev : forall (x y : M.num), x = y -> M.add x M.one = M.add y M.one := by {
      intros x y h
      rw [h]
    }
    apply b2_rev
    apply ih
}

structure IDelta0Model extends BASICModel where
  delta0_induction {n} :
    ∀ (phi_syntax : peano.BoundedFormula Empty (n + 1)),
    isDelta0 phi_syntax ->
    -- phi(0)
    realize_at toBASICModel phi_syntax zero ->
    -- (∀ x : num, φ x -> φ (add x one)) ->
    (forall x : num,
      realize_at toBASICModel phi_syntax x ->
      realize_at toBASICModel phi_syntax (add x one)
    ) ->
    -- ∀ x, φ x
    (forall x : num, realize_at toBASICModel phi_syntax x)


-- Section 3.3.3 Defining y=2^x and BIT(i, x) in IDelta0 (Draft; p.53 of draft, p.64 of pdf)

-- Limited subtraction: The function x -' y := max(0, x - y) is Delta0-definable in IDelta0
-- First, define the relation by the defining axiom
def limited_subtraction_graph_def {a} (x y z : peano.Term a) :=
  max ((y + z = x)) (x <= y ∧ z = 0)

-- z = x -' y IFF ( (y+z=x) or (x <= y AND z = 0)) IFF phi(x, y, z)
-- Then prove uniqueness
IDelta0 proves forall x, forall y, e! z, phi(x, y, z)



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
-- def add_assoc_form :=
-- -- deBruijn indices
--   let x := var_term (2 : Fin 3)
--   let y := var_term (1 : Fin 3)
--   let z := var_term (0 : Fin 3)
--   let lhs := binary_func_term Functions2.add (binary_func_term Functions2.add x y) z
--   let rhs := binary_func_term Functions2.add x (binary_func_term Functions2.add y z)
--   eq_form lhs rhs

-- def add_assoc_form_shallow (M : IOPENModel) := ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)

-- def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]

-- Exercise 3.10 Show that IDelta0 proves the division theorem:
-- IDelta0 |- Forall x y (0 < x -> Exists q . Exists (r < x) . y = x * q + r)

-- def division_form :=
--   let x := var_term (2 : Fin 3)
--   let y := var_term (1 : Fin 3)
--   let z := var_term (0 : Fin 3)
--   let lhs := binary_func_term Functions2.add (binary_func_term Functions2.add x y) z
--   let rhs := binary_func_term Functions2.add x (binary_func_term Functions2.add y z)
--   eq_form lhs rhs

-- def add_assoc_form_shallow (M : IOPENModel) := ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)

-- def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize peano M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]


-- Example 5.44 (The Pairing Function). We define the pairing function
-- ⟨x, y⟩ as the following term of IΔ₀:

-- Exercise 5.45 Show using the results in Section 3.1 that IΔ₀ proves ⟨x, y⟩
-- is a one-one function. That is

-- def IDelta0Model.idelta0_pair x y :=

--   IDelta0Model.mul x y

-- theorem idelta0_pair_one_one (M : IDelta0Model) : forall x1 x2 y1 y2, ⟨x1, y1⟩ = ⟨x2, y2⟩ -> (x1 = x2 ∧ y1 = y2) := by
--   sorry
-- -- (First show that the LHS implies x₁ + y₁ = x₂ + y₂)
