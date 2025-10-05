import Mathlib.Algebra.Regular.Defs

import BoundedArithmetic.IOPEN
import BoundedArithmetic.IDelta0

-- INSTANCES!

universe u v

section IOPEN
variable {M : Type u} [iopen : IOPENModel M]

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
  zero_mul := zero_mul
  mul_zero := B5

instance : CommMonoid M where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

instance : AddCommMonoid M where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := by
    exact B3
  nsmul := nsmulRec
  add_comm := add_comm

instance : Semiring M where
  left_distrib := by
    exact IOPENModel.mul_add
  right_distrib := by
    intro a b c
    rw [<- iopen.mul_comm]
    rw [iopen.mul_add]
    rw [iopen.mul_comm]
    conv => lhs; rhs; rw [iopen.mul_comm]

end IOPEN

section IDelta0

open BASICModel
variable {M : Type u} [idelta0 : IDelta0Model M]

-- D4 used
instance : PartialOrder M where
  le_refl := idelta0.le_refl
  le_trans := @idelta0.le_trans
  le_antisymm := B7
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro hab
      rcases hab with ⟨hle, hne⟩
      constructor
      · exact hle
      · by_contra hba
        apply hne
        apply B7
        exact hle
        exact hba
    · intro h
      rcases h with ⟨hle, hnba⟩
      constructor
      · exact hle
      · by_contra hab
        apply hnba
        rw [hab] at ⊢ hle
        exact hle

instance : CanonicallyOrderedAdd M where
  exists_add_of_le := by
    intro a b hab
    have diff := idelta0.add_diff_exists a b
    obtain ⟨diff, hdiff⟩ := diff
    cases hdiff with
    | inl h => rw [<- h]; exists diff
    | inr h =>
      exists 0
      rw [B3]
      apply B7
      · rw [<- h]
        apply B8
      · exact hab
  le_self_add := B8

instance : IsOrderedAddMonoid M where
  add_le_add_left := fun _ _ a_1 c ↦ add_le_add_left a_1 c

-- D7 used
instance : IsOrderedMonoid M where
  mul_le_mul_left := fun a b h c ↦ by
    rw [mul_comm]
    conv => rhs; rw [mul_comm]
    exact mul_le_mul_right' h c

instance : AddCommMonoid M where


instance : IsOrderedRing M where
  zero_le_one := by exact idelta0.zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a b c hab h_zero_c
    exact mul_le_mul_left' hab c
  mul_le_mul_of_nonneg_right := by
    exact fun a b c a_1 a_2 ↦ idelta0.le_mul_right a_1

instance : CommSemiring M where

noncomputable instance : LinearOrder M where
  le_total := idelta0.le_total
  min_def := by simp only [implies_true]
  max_def := by exact fun a b ↦ rfl
  compare_eq_compareOfLessAndEq := by
    simp only [implies_true]

  toDecidableLE := by
    unfold DecidableLE DecidableRel
    intro a b
    if ha : a = 0 then
      apply Decidable.isTrue
      rw [ha]
      apply zero_le b
    else
      if hb : b = 0 then
        apply Decidable.isFalse
        rw [hb]
        intro ha'
        apply ha
        exact nonpos_iff_eq_zero.mp ha'
      else
        -- HERE, WE SHOULD TAKE PREDECESSOR OF
        -- BOTH AND RECURSE!
        exact Classical.propDecidable (a ≤ b)


-- instance : IsStrictOrderedRing M where
--   le_of_add_le_add_left := by
--     intro a b c h
--     rw [le_cancel_left]
end IDelta0
