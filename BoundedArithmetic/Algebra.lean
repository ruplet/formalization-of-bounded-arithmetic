import Mathlib.Algebra.Regular.Defs

import BoundedArithmetic.IOPEN

-- INSTANCES!

universe u v
variable (M : Type u) [iopen : IOPENModel M]

open BASICModel IOPENModel

theorem isAddRightRegular_one : IsAddRightRegular (1 : M) := by
  unfold IsAddRightRegular Function.Injective
  exact B2

instance : IsRightCancelAdd M where
  add_right_cancel := by
    intro a
    unfold IsAddRightRegular Function.Injective
    intro b c
    simp only
    apply add_cancel_right.mp

instance : MulZeroClass M where
  zero_mul := zero_mul M
  mul_zero := B5

instance : CommMonoid M where
  mul_assoc := mul_assoc M
  one_mul := one_mul M
  mul_one := mul_one M
  mul_comm := mul_comm M

instance : AddCommMonoid M where
  add_assoc := add_assoc M
  zero_add := zero_add M
  add_zero := by
    exact B3
  nsmul := nsmulRec
  add_comm := add_comm M

instance : Semiring M where
  left_distrib := by
    exact fun a b c ↦ IOPENModel.mul_add M a b c
  right_distrib := by
    intro a b c
    rw [<- mul_comm]
    rw [mul_add]
    rw [mul_comm]
    conv => lhs; rhs; rw [mul_comm]
