structure BASICModel where
  -- Sorts
  num    : Type          -- First sort: natural numbers

  -- Functions and predicates for num
  zero   : num
  one    : num
  add    : num → num → num
  mul    : num → num → num
  le     : num → num → Prop
  eqnum  : num → num → Prop := fun x y => x = y

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
  B7 : ∀ (x y : num), le x y → le y x → x = y

  -- B8. x ≤ x + y
  B8 : ∀ (x y : num), le x (add x y)

  C : add zero one = one

structure TwoSortedBASICModel extends BASICModel where
  str    : Type          -- Second sort: binary strings (sets of nums)

  -- Functions and predicates for str
  length : str → num                         -- |X|
  mem    : num → str → Prop                  -- ∈
  eq₂    : str → str → Prop := fun X Y => X = Y

  -- Abbreviation: X(i) := i ∈ X
  X_app  : str → num → Prop := fun X i => mem i X

  -- B9. 0 ≤ x
  B9 : ∀ (x : num), le zero x

  -- B10. x ≤ y ∨ y ≤ x
  B10 : ∀ (x y : num), le x y ∨ le y x

  -- B11. x ≤ y ↔ x < y + 1
  B11 : ∀ (x y : num), le x y ↔ le x (add y one)

  -- B12. x ≠ 0 ⊃ ∃ y ≤ x, y + 1 = x
  B12 : ∀ (x : num), x ≠ zero → ∃ (y : num), le y x ∧ add y one = x

  -- L1. X(i) ⊃ i < |X|
  L1 : ∀ (X : str) (i : num), mem i X → le i (length X)

  -- L2. i + 1 = |X| ⊃ X(i)
  L2 : ∀ (X : str) (i : num), add i one = length X → mem i X

  -- SE. |X| = |Y| ∧ ∀i < |X|, X(i) ↔ Y(i) ⊃ X = Y
  SE : ∀ (X Y : str),
    length X = length Y →
    (∀ (i : num), le i (length X) → mem i X ↔ mem i Y) →
    X = Y
