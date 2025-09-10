-- Cook Nguyen official release, p. 341 of pdf: multiplication in VTC0
-- file:///home/maryjane/papers/CookNguyen.pdf

universe u
class HasLen (str : Type u) (num : Type u) where
  len : str -> num

variable {num str: Type u}
variable [Zero num] [One num] [Add num] [Mul num] [LE num]
variable [HasLen str num] [Membership num str]
variable (seq : num -> str -> num)

-- def allTrue (_ : str) (_ : num) := True

-- instance ie : GetElem str num num allTrue where
--   getElem Z i _ := seq i Z

def pair (x y : num) := (x + y) * (x + y + 1) + (1 + 1) * y
notation "⟨" i "," j "⟩" => pair i j  -- purely a notation alias
local notation "|" Z "|" => HasLen.len Z
local notation Z"["w"]" => seq w Z

instance : LT num where
  lt a b := a <= b ∧ a ≠ b

/-- SEQ'(y,Z): Z is the (lexicographically first) code of a sequence
(i ↦ (Z)i) for all i ≤ y.  This is (226) with `seq` eliminated. --/
def SEQ (y : num) (Z : str) : Prop :=
  ∀ w : num, w < |Z| →
    ( w ∈ Z ↔ ∃ i : num, i <= y ∧ ∃ j : num, j < |Z| ∧ w = ⟨i, j⟩ ∧ j = Z[i] )

/-- The Σ^B_0 body of NUMONES with `seq` eliminated: (227) without `seq`. --/
def NUM_body (y : num) (X Z : str) : Prop :=
  (SEQ seq y Z) ∧
  Z[(0 : num)] = 0 ∧
  (∀ u : num, u < y →
    ( (u ∈ X → Z[u + 1] = Z[u] + 1) ∧
      (¬ u ∈ X → Z[u + 1] = Z[u]) ))

/-- The bounding term from the book: 1 + ⟨y, y⟩. --/
def bound (y : num) : num := 1 + ⟨y, y⟩

/-- The NUMONES axiom, as a single Σ^B_0-style existence over strings. --/
def NUMONES_ax (y : num) (X : str) : Prop :=
  ∃ Z : str, |Z| <= bound y ∧ NUM_body seq y X Z


structure VTC0 where
  -- Arithmetic (numbers)
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

  -- Optional convenience axiom from your previous bundle (harmless to keep):
  c   : (0 : num) + 1 = 1

  -- Strings (bits/length)
  l1  : ∀ (X : str) (y : num), y ∈ X → y < |X|
  l2  : ∀ (X : str) (y : num), y + 1 = |X| → y ∈ X
  se  : ∀ (X Y : str),
          ((|X| = HasLen.len (num := num) Y ) ∧ ∀ (i : num), i < |X| → (i ∈ X ↔ i ∈ Y)) → X = Y
  -- notation (71)
  -- this is provable
  seq_ax : ∀ (x : num) (Z : str) (y : num),
    y = seq x Z ↔ ( (y < |Z| ∧ ⟨x, y⟩ ∈ Z ∧ ∀ z : num, z < y → ¬ ⟨x, z⟩ ∈ Z)          -- first hit at y
          ∨
          ( (∀ z : num, z < |Z| → ¬ ⟨x, z⟩ ∈ Z) ∧ y = |Z| ) )            -- none found ⇒ y = |Z|

  -- V.4.21, provable!
  pair_inj :
    ∀ x1 y1 x2 y2 : num, ⟨x1, y1⟩ = ⟨x2, y2⟩ → x1 = x2 ∧ y1 = y2

  numones : ∀ (y : num) (X : str), NUMONES_ax seq y X

section

theorem leq_refl (h : VTC0 seq) : ∀ x : num, x <= x := by
  intro x
  conv => right; rw [<- h.b3 x]
  apply h.b8

end
