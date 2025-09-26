import Mathlib.ModelTheory.Semantics
import BoundedArithmetic.LanguagePeano

open FirstOrder FirstOrder.Language

-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
-- semi-bundled design! inspired by mathlib Ring
-- extending peano.Structure instead of One, Add, ... is needed to .Realize
class BASICModel (num : Type*) extends peano.Structure num where
  B1 : ∀ x   : num, (x + 1) ≠ 0
  B2 : ∀ x y : num, (x + 1) = (y + 1) -> x = y
  B3 : ∀ x   : num, x + 0 = x
  B4 : ∀ x y : num, x + (y + 1) = (x + y) + 1
  B5 : ∀ x   : num, x * 0 = 0
  B6 : ∀ x y : num, x * (y + 1) = x * y + x
  B7 : ∀ x y : num, x <= y ∧ y <= x -> x = y
  B8 : ∀ x y : num, x <= x + y
  C  : (0 : num) + 1 = 1

instance (M : Type*) [BASICModel M] : Zero M where
  zero := 0

instance (M : Type*) [BASICModel M] : Add M where
  add x y := x + y

instance (M : Type*) [BASICModel M] : Mul M where
  mul x y := x * y

instance (M : Type*) [BASICModel M] : LE M where
  le x y := x <= y

instance (M : Type*) [BASICModel M] : LT M where
  lt x y := x <= y ∧ x ≠ y

namespace BASICModel
universe u
variable (M : Type u) [iopen : BASICModel M]

-- this is axctually O9. x ≤ x from Logical Foundations
theorem le_refl : ∀ a : M, a <= a := by
  intro x
  conv => right; rw [<- B3 x]
  apply B8

theorem zero_ne_add_one : ∀ x : M, x + 1 ≠ 0 := B1
theorem one_add_right_regular : IsAddRightRegular (1 : M) := B2


end BASICModel
