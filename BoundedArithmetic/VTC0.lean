import Mathlib.Init
-- This file sketches the proof of VTC⁰(numones) ⊢ PHP(a, X)
-- This demonstrates that VTC⁰ proves the Pigeonhole Principle
-- It defines the necessary definitions and auxiliary lemmas,
-- rather faithfully following Theorem IX.3.23 at p. 291 of Cook, Nguyen 2010

-- This is the first of the interesting theorems that we aim to
-- formalize inside of VTC⁰. The other ones from Cook, Nguyen are:
-- - sorting: prove that VTC0 proves that `rank` is provably total
--   (Ex. IX.3.9, p.287)
-- - defining binary multiplication and proving its basic properties
-- - Finite Szpilrajn's Theorem!

-- TODOs:
-- - of course we need to define this while in ModelTheory-matching style
-- - provide nice machinery for extending V^0 with V^0-definable functions
--   and predicates! This will get rid of `seq` and `numones` axioms
-- - fix the ugly section-variables passing (passing `seq` as arg. everywhere)

universe u
variable {num str: Type u}
variable [Zero num] [One num] [Add num] [Mul num] [LE num] [Membership num str]

class HasLen (str : Type u) (num : Type u) where
  len : str -> num
variable [HasLen str num]

-- we add seq and numones as special symbols for fast prototyping,
-- although they are definable in V^0
variable (seq : num -> str -> num) (numones : num -> str -> num)

def pair (x y : num) := (x + y) * (x + y + 1) + (1 + 1) * y

notation "⟨" i "," j "⟩" => pair i j
local notation "|" Z "|" => HasLen.len Z
local notation Z"["w"]" => seq w Z

instance : LT num where
  lt a b := a <= b ∧ a ≠ b

/-- SEQ'(y,Z): Z is the (lexicographically first) code of a sequence
(i ↦ (Z)i) for all i ≤ y.  This is (226); we don't eliminate seq, because
we added is as a new symbol to the theory --/
def SEQ (y : num) (Z : str) : Prop :=
  ∀ w : num, w < |Z| →
    ( w ∈ Z ↔ ∃ i : num, i <= y ∧ ∃ j : num, j < |Z| ∧ w = ⟨i, j⟩ ∧ j = Z[i] )

/-- The body of NUMONES (227) --/
def NUM_body (y : num) (X Z : str) : Prop :=
  (SEQ seq y Z) ∧
  Z[(0 : num)] = 0 ∧
  (∀ u : num, u < y →
    ( (u ∈ X → Z[u + 1] = Z[u] + 1) ∧
      (¬ u ∈ X → Z[u + 1] = Z[u]) ))

/-- The bounding term from the book: 1 + ⟨y, y⟩. --/
@[inline] def bound (y : num) : num := 1 + ⟨y, y⟩

/-- The NUMONES axiom, Definition IX.3.2 --/
def NUMONES_ax (y : num) (X : str) : Prop :=
  ∃ Z : str, |Z| <= bound y ∧ NUM_body seq y X Z

/-- Cook–Nguyen (108): graph of the number function `numones`. --/
def numones_ax (seq : num → str → num) (y : num) (X : str) (z : num) : Prop :=
  z ≤ y ∧
  ∃ Z : str, |Z| ≤ bound y ∧
    ( -- base and final value
      seq 0 Z = 0 ∧
      seq y Z = z ∧
      -- recurrence for 0 ≤ u < y
      ∀ u : num, u < y →
        ((u ∈ X → seq (u+1) Z = seq u Z + 1) ∧
         (¬ u ∈ X → seq (u+1) Z = seq u Z)) )


structure VTC0 where
  b1  : ∀ x : num, x + (1 : num) ≠ 0
  b2  : ∀ x y : num, x + 1 = y + 1 → x = y
  b3  : ∀ x : num, x + 0 = x
  b4  : ∀ x y : num, x + (y + 1) = (x + y) + 1
  b5  : ∀ x : num, x * 0 = 0
  b6  : ∀ x y : num, x * (y + 1) = (x * y) + x
  b7  : ∀ x y : num, x ≤ y ∧ y ≤ x → x = y
  b8  : ∀ x y : num, x ≤ x + y
  b9  : ∀ x : num, 0 ≤ x
  b10 : ∀ x y : num, x ≤ y ∨ y ≤ x
  b11 : ∀ x y : num, x ≤ y ↔ x < y + 1
  b12 : ∀ x : num, x ≠ 0 → ∃ y : num, y ≤ x ∧ y + 1 = x

  c   : (0 : num) + 1 = 1

  l1  : ∀ (X : str) (y : num), y ∈ X → y < |X|
  l2  : ∀ (X : str) (y : num), y + 1 = |X| → y ∈ X
  se  : ∀ (X Y : str),
          ((|X| = HasLen.len (num := num) Y ) ∧ ∀ (i : num), i < |X| → (i ∈ X ↔ i ∈ Y)) → X = Y

  -- notation (71)
  -- this is provable
  seq_ax : ∀ (x : num) (Z : str) (y : num),
    y = seq x Z ↔ ( (y < |Z| ∧ ⟨x, y⟩ ∈ Z ∧ ∀ z : num, z < y → ¬ ⟨x, z⟩ ∈ Z)
          ∨
          ( (∀ z : num, z < |Z| → ¬ ⟨x, z⟩ ∈ Z) ∧ y = |Z| ) )

  -- V.4.21, provable!
  pair_inj :
    ∀ x1 y1 x2 y2 : num, ⟨x1, y1⟩ = ⟨x2, y2⟩ → x1 = x2 ∧ y1 = y2

  -- these two also don't have to be axioms
  NUMONES : ∀ (y : num) (X : str), NUMONES_ax seq y X
  numones : ∀ (y z : num) (X : str), numones y X = z ↔ numones_ax seq y X z


section

-- demo
theorem leq_refl (h : VTC0 seq numones) : ∀ x : num, x <= x := by
  intro x
  conv => right; rw [<- h.b3 x]
  apply h.b8

-- The Pigeonhole Principle (PHP), Cook-Nguyen (242)
-- X(i, j) := ⟨i, j⟩ ∈ X IFF pigeon `i` gets placed in hole `j`
def PHP (a : num) (X : str) : Prop :=
  ( (∀ x : num, x ≤ a → ∃ y : num, y < a ∧ ⟨x, y⟩ ∈ X) →
    ∃ x, x ≤ a ∧ ∃ z, z ≤ a ∧ ∃ y, y < a ∧ x ≠ z ∧ ⟨x, y⟩ ∈ X ∧ ⟨z, y⟩ ∈ X )

notation X"(" x ", " y ")" => ⟨x, y⟩ ∈ X

/-- “First hole” formula ϕ(x,y): y is the first hole < a that x occupies. -/
def FirstHole (a : num) (X : str) (x y : num) : Prop :=
  x ≤ a ∧ y < a ∧ X(x,y) ∧ ∀ v : num, v < y → ¬ X(x,v)

-- (243): coverage hypothesis
def Cover (a : num) (X : str) : Prop :=
  ∀ x, x ≤ a → ∃ y, y < a ∧ X(x,y)

-- (244): no-collision hypothesis
def NoCollision (a : num) (X : str) : Prop :=
  ∀ x, x ≤ a → ∀ z, z ≤ a → ∀ y, y < a → ((x ≠ z ∧ X(x,y)) → ¬ X(z,y))

-- this is in mathlib
def ExistsUnique (p : num → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
syntax "∃!" ident ", " term : term
macro_rules
  | `(∃! $x:ident, $p) =>
      `(ExistsUnique (fun $x => $p))

theorem firstHole_exists_unique
  {a : num} {X : str}
  (hCover : Cover a X)
  (hNoCol : NoCollision a X) :
  ∀ x, x ≤ a → ∃!y, (y < a ∧ FirstHole a X x y) :=
by
  sorry

/-- 2) Injectivity of ϕ across different pigeons (from NoCollision). -/
theorem firstHole_injective
  {a : num} {X : str}
  (hCover : Cover a X)
  (hNoCol : NoCollision a X) :
  ∀x, x ≤ a → ∀ z, z ≤ a → ∀ y, y < a →
    (x ≠ z ∧ FirstHole a X x y) → ¬ FirstHole a X z y :=
by
  -- Proof sketch:
  --  If FirstHole a X x y and x ≠ z, then X(x,y) and no earlier v< y has X(x,v).
  --  hNoCol gives ¬X(z,y), hence ¬ FirstHole a X z y.
  sorry

def image_def (a : num) (X H : str) :=
  |H| ≤ a ∧
    ∀ y, y < a → (y ∈ H ↔ ∃ x, x ≤ a ∧ FirstHole a X x y)

theorem image_exists
  {a : num} {X : str} :
  ∃ H : str, image_def a X H := by
  -- by comprehension!
  sorry

/-- 5) A “segment” string P for `{0,…,a}` and its numones. -/
def pigeons_def (a : num) (P : str) :=
  |P| = a + 1 ∧ ∀ y, y < |P| → (y ∈ P ↔ y ≤ a)

theorem segment_exists (a : num) :
  ∃ P : str, pigeons_def a P := by
  -- by comprehension.
  sorry

theorem numones_segment (a : num) :
  ∀ {P : str}, pigeons_def a P →
  numones (a + 1) P = a + 1 := by
  sorry

/-- 6) Upper bound for the image `H`: it only uses holes `< a`, so
    `numones (a+1) H ≤ a`. -/
theorem numones_image_le (a : num) (X H : str) (himage_def : image_def a X H):
  numones (a + 1) H ≤ a := by
  sorry

-- Theorem IX.3.23. VTC^0 ⊢ PHP(a, X).
-- please ignore `seq, numones, hVTC0` arguments, they're a pure technicaly
-- `a`: number of holes
-- `X`: 2D array with `X(i, j)` holds iff pigeon `i` is in hole `j`
theorem PigeonholePrinciple (seq : num -> str -> num) (numones : num -> str -> num) (hVTC0 : VTC0 seq numones)
  (a : num) (X : str)
: PHP a X :=
by
  intro hCover
  false_or_by_contra
  rename_i hInj
  simp only [not_exists, not_and] at hInj

  have hInj' : NoCollision a X := by
    unfold NoCollision
    intro x hx y hy z hz hn
    obtain ⟨hnl, hnr⟩ := hn
    apply hInj x hx y hy z hz hnl hnr

  have hFirstHoleExUnique := firstHole_exists_unique hCover hInj'
  have hFirstHoleInjective := firstHole_injective hCover hInj'
  obtain ⟨H, hH⟩ := image_exists (a := a) (X := X)
  obtain ⟨P, hP⟩ := segment_exists (num := num) (str := str) a

  -- From Lemma IX.3.24: P and H have the same cardinality:
  have card_P_eq_card_H : numones (a + 1) P = numones (a + 1) H := by
    sorry

  rw [numones_segment numones a hP] at card_P_eq_card_H
  -- have aux := leq_refl seq numones hVTC0 (a + 1)
  have a_lt_numones_H : a < a + 1 := by
    rw [<- VTC0.b11 (num := num) (str := str) (seq := seq) (numones := numones) (self := hVTC0)]
    apply leq_refl seq numones hVTC0 a
  rw [card_P_eq_card_H] at a_lt_numones_H
  have a_ge_numones_H := numones_image_le numones a X H hH

  unfold LT.lt at a_lt_numones_H
  obtain ⟨a_le_numones_H, a_neq_numones_H⟩ := a_lt_numones_H
  have a_eq_numones_H :=
    VTC0.b7
    (num := num) (str := str) (seq := seq) (numones := numones) (self := hVTC0)
    a (numones (a + 1) H)

  apply a_neq_numones_H
  apply a_eq_numones_H
  constructor
  · exact a_le_numones_H
  · exact a_ge_numones_H

end
