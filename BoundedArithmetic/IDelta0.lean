import BoundedArithmetic.BoundedModelTheory.Basic
import BoundedArithmetic.BoundedModelTheory.Syntax
import BoundedArithmetic.BoundedModelTheory.Complexity
-- import BoundedArithmetic.BoundedModelTheory.Semantics

namespace L2

inductive Functions0 where
| zero
| one
deriving BEq, DecidableEq

inductive Functions2 where
| add
| mul
deriving BEq, DecidableEq

inductive Relations2 where
-- | eqnum
| leq
deriving BEq, DecidableEq

def Functions (arity : Nat) : Type :=
  match arity with
  | 0 => Functions0
  | 2 => Functions2
  | _ => Empty


def Relations (arity : Nat) : Type :=
  match arity with
  | 2 => Relations2
  | _ => Empty

def Lang : FirstOrder.Language :=
{ Functions := Functions,
  Relations := Relations
}

open FirstOrder.Language (Term BoundedFormula Formula Sentence)

-- def isOpen {a} [DecidableEq a] {n} (sentence: Lang.BoundedFormula a n) : Bool :=
-- match sentence with
-- | .falsum => true
-- | .equal _ _ => false -- please use our internal equation symbol!
-- | .rel _ _ => true
-- | .imp pre post => isOpen pre ∧ isOpen post
-- | .all _ => false

def isOpen {a} {n} [DecidableEq a] (formula : Lang.BoundedFormula a n) := FirstOrder.Language.BoundedFormula.IsQF formula

def contains_var_zero {a} [DecidableEq a] {n} (t : Lang.Term (a ⊕ Fin n)) : Bool :=
  if h_eq : n = 0 then
    false
  else
    (Sum.inr $ @Fin.mk n 0 (Nat.pos_of_ne_zero h_eq)) ∈ t.varFinset

def is_x_le_t_imp_A {a} [DecidableEq a] {n} [NeZero n] (f : Lang.BoundedFormula a n) : Bool :=
  match f with
  | BoundedFormula.imp pre _ =>
    match pre with
    | @BoundedFormula.rel _ _ _ l R ts =>
      if h_eq_2 : l = 2 then
        let relationLeq : Lang.Relations 2 := Relations2.leq
        let R_as_rel2 : Relations2 := Eq.mp (congrArg Lang.Relations h_eq_2) R
        let term_vec_type (k : ℕ) := Fin k → Term Lang (a ⊕ (Fin n))
        let ts_as_fin2 : term_vec_type 2 := Eq.mp (congrArg term_vec_type h_eq_2) ts
        if R_as_rel2 == relationLeq then
          let x_term := ts_as_fin2 (0 : Fin 2)
          let t_term := ts_as_fin2 (1 : Fin 2)
          -- Check if x_term is the de Bruijn index 0
          (match x_term with
           | Term.var (Sum.inr j) => j == (Fin.ofNat n 0)
           | _ => false) &&
          -- Check if t_term does NOT contain the de Bruijn index 0
          !(contains_var_zero t_term)
        else false
      else false
    | _ => false
  | _ => false

def isDelta0 {a} [DecidableEq a] {n} [NeZero n] : Lang.BoundedFormula a n -> Bool
| .falsum => true
| .equal _ _=> false
| .rel _ _ => true
| .imp pre post => isDelta0 pre ∧ isDelta0 post
| .ex phi =>
  (is_x_le_t_imp_A phi) ∧ (isDelta0 phi) -- Recursively check inner formula
| .all phi =>
  (is_x_le_t_imp_A phi) ∧ (isDelta0 phi)

-- def relationEq : Lang.Relations 2 := Relations2.eqnum
def relationLeq : Lang.Relations 2 := Relations2.leq

-- --- Sentence Construction Helpers ---
-- For sentences, α is Empty, and n is 0.

-- A variable term (for current context `n`).
-- For sentences, `n = 0`, so `Fin 0` is `Empty`.
-- If we're inside `all {n} f`, then `f` has context `n+1`, so `Fin (n+1)`.
def var_term {k : ℕ} (idx : Fin k) : Term Lang (Empty ⊕ (Fin k)) := Term.var (Sum.inr idx)

-- A constant term. Now `k` is a free variable, so Lean can infer it.
-- This term type is `Term Lang (α ⊕ (Fin k))`
def const_term {α} {k : ℕ} (c : Lang.Functions 0) : Term Lang (α ⊕ (Fin k)) := Term.func c ![]

-- A term from a binary function (e.g., add, mul). `k` is also generic here.
def binary_func_term {α} {k : ℕ} (f : Lang.Functions 2) (t1 t2 : Term Lang (α ⊕ (Fin k))) : Term Lang (α ⊕ (Fin k)) := Term.func f ![t1, t2]

-- Atomic formulas
def eq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.equal t1 t2

def leq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationLeq ![t1, t2]

def falsum_form {a} {k : ℕ} : Lang.BoundedFormula a k := BoundedFormula.falsum

def imp_form {a} {k : ℕ} (f1 f2 : BoundedFormula Lang a k) : BoundedFormula Lang a k :=
  BoundedFormula.imp f1 f2

def all_form {a} {k : ℕ} (f : BoundedFormula Lang a (k + 1)) : BoundedFormula Lang a k :=
  BoundedFormula.all f

-- --- Example Sentences ---

-- 1. Open Sentences (no quantifiers)

def funcZero : Lang.Functions 0 := Functions0.zero
def funcOne : Lang.Functions 0 := Functions0.one
def funcAdd : Lang.Functions 2 := Functions2.add
def funcMul : Lang.Functions 2 := Functions2.mul

-- 0 = 1 (false)
def open_s_1 : Sentence Lang :=
  eq_form (const_term funcZero) (const_term funcOne)

-- 0 <= 0 (true)
def open_s_2 : Sentence Lang :=
  leq_form (const_term funcZero) (const_term funcZero)

-- (0 <= 1) -> (1 = 0)
def open_s_3 : Sentence Lang :=
  imp_form (leq_form (const_term funcZero) (const_term funcOne))
           (eq_form (const_term funcOne) (const_term funcZero))

-- `x = 0` (deep embedding)
def open_x_eq_zero : BoundedFormula Lang Empty 1 :=
  eq_form (var_term (Fin.mk 0 Nat.zero_lt_one)) (const_term (k := 1) funcZero)

-- `x ≤ 0` (deep embedding)
def open_x_le_zero_form : BoundedFormula Lang Empty 1 :=
  leq_form (var_term (Fin.mk 0 Nat.zero_lt_one)) (const_term (k := 1) funcZero)

-- 2. Delta0 Sentences (only bounded quantifiers)

-- ∀x (x <= 1 -> x = 0)
-- Here, x corresponds to the de Bruijn index 0 in the inner formula.
-- '1' is the constant `funcOne`.
def delta0_s_1 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) (const_term funcOne))
                     (eq_form (var_term (0 : Fin 1)) (const_term funcZero)))

-- ∀x (x <= 1 -> (x = 0 -> x <= 1))
def delta0_s_2 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) (const_term funcOne))
                     (imp_form (eq_form (var_term (0 : Fin 1)) (const_term funcZero))
                               (leq_form (var_term (0 : Fin 1)) (const_term funcOne))))

-- ∀x (x <= y -> x = 0) -- This is NOT a sentence because 'y' is a free variable (unless y is 0 here)
-- Let's make it a proper sentence: ∀x (x <= 1 + 1 -> x = 0)
-- The term `1 + 1` should not contain `x` (de Bruijn index 0).
def term_one_plus_one : Term Lang (Empty ⊕ (Fin 1)) :=
  binary_func_term funcAdd (const_term funcOne) (const_term funcOne)

def delta0_s_3 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) term_one_plus_one)
                     (eq_form (var_term (0 : Fin 1)) (const_term funcZero)))


-- 3. Pi1 Sentences (block of universal quantifiers, inner formula is Delta0)

-- ∀x (x = x) -- This is Pi1 (vacuously Delta0 inside) and also not Delta0 (unbounded quantifier)
def pi1_s_1 : Sentence Lang :=
  all_form (eq_form (var_term (0 : Fin 1)) (var_term (0 : Fin 1)))

-- ∀x (∀y (x <= y -> x = x)) -- This is Pi1 (inner is Delta0, outer is unbounded)
-- The `(0 : Fin 1)` refers to `y`, `(1 : Fin 2)` refers to `x` in the `Fin 2` context
def pi1_s_2 : Sentence Lang :=
  all_form (all_form (imp_form (leq_form (var_term (1 : Fin 2)) (var_term (0 : Fin 2))) -- x <= y
                                (eq_form (var_term (1 : Fin 2)) (var_term (1 : Fin 2))))) -- x = x

-- Let's make a Pi1 where the inner formula is a full Delta0 formula with its own bounded quantifier
-- ∀z (∀x (x <= 1 -> x = 0)) -- This is Pi1, the outermost `z` is unbounded
def pi1_s_3 : Sentence Lang :=
  all_form (all_form (imp_form (leq_form (var_term (0 : Fin 2)) (const_term funcOne))
                                (eq_form (var_term (0 : Fin 2)) (const_term funcZero))))

-- --- Test Cases ---

theorem ex1 : isOpen open_s_1 := by {
  unfold open_s_1 eq_form
  apply FirstOrder.Language.BoundedFormula.IsQF.of_isAtomic
  apply FirstOrder.Language.BoundedFormula.IsAtomic.equal
}

-- -- #eval isOpen open_s_1   -- Expected: true
-- #eval isDelta0 open_s_1 -- Expected: true (open formulas are vacuously Delta0)

-- #eval isOpen open_s_2   -- Expected: true
-- #eval isDelta0 open_s_2 -- Expected: true

-- #eval isOpen open_s_3   -- Expected: true
-- #eval isDelta0 open_s_3 -- Expected: true

-- #eval isOpen open_x_eq_zero
-- #eval isDelta0 open_x_eq_zero

-- #eval isOpen open_x_le_zero_form
-- #eval isDelta0 open_x_le_zero_form

-- #eval isOpen delta0_s_1   -- Expected: false
-- #eval isDelta0 delta0_s_1 -- Expected: true

-- #eval isOpen delta0_s_2   -- Expected: false
-- #eval isDelta0 delta0_s_2 -- Expected: true

-- #eval isOpen delta0_s_3   -- Expected: false
-- #eval isDelta0 delta0_s_3 -- Expected: true

-- #eval isOpen pi1_s_1    -- Expected: false
-- #eval isDelta0 pi1_s_1    -- Expected: false (unbounded quantifier)

-- #eval isOpen pi1_s_2    -- Expected: false
-- #eval isDelta0 pi1_s_2    -- Expected: false (outer quantifier is unbounded)

-- #eval isOpen pi1_s_3    -- Expected: false
-- #eval isDelta0 pi1_s_3    -- Expected: false (outermost quantifier is unbounded)


-- Section 3.1 Peano Arithmetic (Draft, page 34 (45 of pdf))

structure BASICModel where
  -- Sorts
  num    : Type          -- First sort: natural numbers

  -- Functions and predicates for num
  zero   : num
  one    : num
  add    : num → num → num
  mul    : num → num → num
  leq    : num → num → Prop
  -- eqnum  : num → num → Prop := fun x y => x = y

  -- B1. x + 1 ≠ 0
  B1 : ∀ (x : num), add x one ≠ zero

  -- B2. x + 1 = y + 1 ⊃ x = y
  B2 : ∀ (x y : num), add x one = add y one → x = y

  -- B3. x + 0 = x
  B3 : ∀ (x : num), add x zero = x

  -- B4. x + (y + 1) = (x + y) + 1
  B4 : ∀ (x y : num), add x (add y one) = add (add x y) one

  -- B5. x · 0 = 0
  B5 : ∀ (x : num), mul x zero = zero

  -- B6. x · (y + 1) = (x · y) + x
  B6 : ∀ (x y : num), mul x (add y one) = add (mul x y) x

  -- B7. (x ≤ y ∧ y ≤ x) ⊃ x = y
  B7 : ∀ (x y : num), leq x y → leq y x → x = y

  -- B8. x ≤ x + y
  B8 : ∀ (x y : num), leq x (add x y)

  -- C. 0 + 1 = 1
  C : add zero one = one


instance BASICModel_Structure (M : BASICModel) : Lang.Structure M.num :=
{
  -- Carrier := fun _ => M.num,
  funMap := fun {arity} f =>
    match arity, f with
    | 0, Functions0.zero => fun _ => M.zero
    | 0, Functions0.one => fun _ => M.one
    | 2, Functions2.add => fun args => M.add (args 0) (args 1)
    | 2, Functions2.mul => fun args => M.mul (args 0) (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    -- | 2, Relations2.eqnum => fun args => M.eqnum (args 0) (args 1)
    | 2, Relations2.leq => fun args => M.leq (args 0) (args 1)
}

def realize_at : forall {n}, (M : BASICModel) -> Lang.BoundedFormula Empty (n + 1) -> M.num -> Prop
| 0, M, phi, term => @phi.Realize Lang M.num (BASICModel_Structure M) _ _ (Empty.elim) ![term]
| _ + 1, M, phi, term => realize_at M phi.all term

structure IOPENModel extends BASICModel where
  open_induction {n} :
    ∀ (phi_syntax : Lang.BoundedFormula Empty (n + 1)),
    isOpen phi_syntax ->
    -- phi(0)
    realize_at toBASICModel phi_syntax zero ->
    -- (∀ x : num, φ x → φ (add x one)) →
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

def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize Lang M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]

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
    simp [FirstOrder.Language.Structure.funMap, Fin.snoc]
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
    simp [FirstOrder.Language.Structure.funMap, Fin.snoc] at h
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
    simp [FirstOrder.Language.Structure.funMap, Fin.snoc]
    -- use B3. x + 0 = x
    rw [M.B3 (M.add b a)]
    rw [M.B3 a]
  -- prove that forall x, (phi(x) -> phi(x + 1))
  · intros x ih
    unfold add_assoc_form
    simp [realize_at]
    intros y z
    simp [BoundedFormula.Realize, eq_form, binary_func_term, var_term]
    simp [FirstOrder.Language.Structure.funMap, Fin.snoc]
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
    ∀ (phi_syntax : Lang.BoundedFormula Empty (n + 1)),
    isDelta0 phi_syntax ->
    -- phi(0)
    realize_at toBASICModel phi_syntax zero ->
    -- (∀ x : num, φ x → φ (add x one)) →
    (forall x : num,
      realize_at toBASICModel phi_syntax x ->
      realize_at toBASICModel phi_syntax (add x one)
    ) ->
    -- ∀ x, φ x
    (forall x : num, realize_at toBASICModel phi_syntax x)


-- Example 3.9 The following formulas (and their universal closures) are theorems of IDelta0:
-- D1. x neq 0 -> Exists y<=x . (x = y + 1) (Predecessor)
-- proof: induction on x
-- def pred_form :=
--   -- let x := var_term (1 : Fin 2)
--   -- let y := var_term (0 : Fin 2) -- y will actually be bound by a quatifier
--   let xneq0 := BoundedFormula.not $ BoundedFormula.equal (var_term (0 : Fin 2)) (const_term funcZero) -- here 'y' means actually our 'x'!!!! (deBruijn indices)
--   let rhs : Lang.BoundedFormula Empty 2 := BoundedFormula.ex
--     (max
--       (BoundedFormula.rel relationLeq ![var_term (0 : Fin 2), var_term (1 : Fin 2)])
--       (BoundedFormula.equal
--         (var_term (1 : Fin 2))
--         (Term.func funcAdd ![var_term (0 : Fin 2), const_term funcOne]))
--     )
--   imp_form xneq0 rhs

-- def pred_form_shallow (M : IDelta0Model) := ∀ x, (x ≠ M.zero) -> ∃ y , (M.leq y x ∧ x = M.add x M.one)

-- def pred_form_deep (M : IDelta0Model) := @BoundedFormula.Realize Lang M.num (BASICModel_Structure M.toBASICModel) _ _ (pred_form.alls) (Empty.elim) ![]

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
--     simp [FirstOrder.Language.Structure.funMap, Fin.snoc]
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

-- def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize Lang M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]

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

-- def add_assoc_form_deep (M : IOPENModel) := @BoundedFormula.Realize Lang M.num (BASICModel_Structure M.toBASICModel) _ _ (add_assoc_form.alls) (Empty.elim) ![]


-- Example 5.44 (The Pairing Function). We define the pairing function
-- ⟨x, y⟩ as the following term of IΔ₀:

-- Exercise 5.45 Show using the results in Section 3.1 that IΔ₀ proves ⟨x, y⟩
-- is a one-one function. That is

-- def IDelta0Model.idelta0_pair x y :=

--   IDelta0Model.mul x y

-- theorem idelta0_pair_one_one (M : IDelta0Model) : forall x1 x2 y1 y2, ⟨x1, y1⟩ = ⟨x2, y2⟩ -> (x1 = x2 ∧ y1 = y2) := by
--   sorry
-- -- (First show that the LHS implies x₁ + y₁ = x₂ + y₂)
