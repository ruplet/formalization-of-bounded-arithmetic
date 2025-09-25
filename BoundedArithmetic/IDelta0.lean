import Mathlib.Algebra.Ring.Defs

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.IsEnum
import BoundedArithmetic.IsEnumProperties
import BoundedArithmetic.IOPEN

open FirstOrder Language BoundedFormula

class IDelta0Model (num : Type*) extends IOPENModel num where
  delta0_induction {disp} [HasDisplayed disp] {a} [IsEnum a]
    (phi : peano.BoundedFormula (disp ⊕ a) 0) :
    phi.IsDelta0 -> (mkInductionSentence phi).Realize num

namespace IDelta0Model

universe u
variable (M : Type) [idelta0 : IDelta0Model M]


-- Example 3.9 Theorems of IΔ0
-- TODO: not fixing the 'num'(?) universe level to 0 breaks everything.
-- learn how to do universe polymorphism properly and fix this
-- these two 0s correspond to universe level of vars; last is Empty

instance a : IsEnum Empty where
  size := 0
  toIdx := Empty.elim
  fromIdx := Fin.elim0
  to_from_id := by simp only [IsEmpty.forall_iff]
  from_to_id := by simp only [IsEmpty.forall_iff]

open Formula BoundedFormula

open BASICModel IOPENModel

-- D1. x ≠ 0 → ∃ y ≤ x, x = y + 1  (Predecessor)
-- proof: induction on x
theorem pred_exists :
  ∀ x : M, x ≠ 0 → ∃ y ≤ x, x = y + 1 :=
by
  let ind1 : peano.Formula Vars2xy := x =' (y + (1 : peano.Term _))
  let ind2 : peano.Formula Vars1x :=
    (Formula.iBdEx' x (display_y_xy ind1).flip)
  let ind3 : peano.Formula (Vars1x ⊕ Empty) :=
    display_x_x $ (x ≠' 0) ⟹ ind2
  let ind := delta0_induction (a := Empty) (self := idelta0) ind3

  -- unfold c b a at ind
  unfold ind3 ind2 ind1 mkInductionSentence at ind
  unfold Sentence.Realize Formula.Realize iAlls' BoundedFormula.alls at ind
  conv at ind =>
    rhs;
    unfold iBdEx' exs alls
    unfold exs alls Term.neq
    simp [delta0_simps]

  intro x hx
  apply ind
  · unfold display_x_x display_y_xy BoundedFormula.flip display
    rw [<- IsDelta0.relabelEquiv]
    apply IsDelta0.imp
    · constructor
      · constructor
        apply IsQF.of_isAtomic
        apply IsAtomic.equal
      · constructor
        exact isQF_bot
    · apply IsDelta0.bdEx
  · intro a hind ha
    exists a
    constructor
    · exact B8 a 1
    · exact rfl
  · exact hx

theorem ex_lt {a} [LE a] {t} {P : a -> Prop} : (∃ x ≤ t, P x) -> ∃ x, P x := by
  intro h
  obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
  exists x

lemma zero_add :
  ∀ x : M, 0 + x = x :=
by
  intro x
  rw [add_comm]
  exact B3 x

-- D2. ∃ z, (x + z = y ∨ y + z = x)
-- original proof: Induction on x. Base case: B2, O2. Induction step: B3, B4, D1
-- our proof is different
theorem add_diff_exists :
  ∀ x y : M, ∃ z, x + z = y ∨ y + z = x :=
by
  let ind1 : peano.Formula _ := display_z_xyz $ ((x + z) =' y) ⊔ ((y + z) =' x)
  let ind2 := display_x_xy $ iBdEx' (x + y) $ ind1.flip
  let ind := delta0_induction (self := idelta0) ind2

  unfold ind2 ind1 at ind
  unfold display_x_xy at ind
  rw [<- IsDelta0.relabelEquiv] at ind
  conv at ind =>
    rhs;
    unfold iBdEx'
    simp [delta0_simps]

  intro x y
  apply ex_lt
  apply ind
  · apply IsDelta0.bdEx
  · intro z
    exists z
    constructor
    · exact BASICModel.le_refl M z
    · rw [add_comm]
      left
      rfl
  · intro L hind R
    by_cases h_R_zero : R = 0
    · exists (L + 1)
      constructor
      · exact B8 (L + 1) R
      · right
        rw [h_R_zero]
        rw [zero_add]
    · obtain ⟨pred_R, h_pred_R_le, h_pred_R_eq⟩ := pred_exists M R h_R_zero
      specialize hind pred_R
      obtain ⟨symdiff_pred, h_symdiff_pred_le, h_symdiff_pred_eq⟩ := hind
      exists symdiff_pred
      cases h_symdiff_pred_eq with
      | inl h_LR =>
        constructor
        · rw [h_pred_R_eq, <- h_LR]
          rw [add_rotate']
          conv => rhs; lhs; rw [add_comm]
          rw [add_assoc]
          apply B8
        · left
          rw [h_pred_R_eq]
          rw [add_assoc]
          conv => lhs; rhs; rw [add_comm]
          rw [<- add_assoc]
          congr
      | inr h_RL =>
        constructor
        · rw [<- h_RL]
          conv => rhs; left; left; rw [add_comm]
          conv => rhs; left; rw [add_comm]; rw [<- add_assoc]; left; rw [add_comm]
          conv => rhs; rw [add_assoc]; rw [add_assoc]
          apply B8
        · -- L = R - 1 + X, czyli
          -- L + 1 + X + 1 = R?
          -- R + X = L?
          right
          rw [<- h_RL]
          rw [h_pred_R_eq]
          conv => lhs; rw [add_assoc]; rhs; rw [add_comm]
          rw [add_assoc]


-- D3. x ≤ y ↔ ∃ z, x + z = y
theorem le_iff_exists_add :
  ∀ x y : M, x ≤ y ↔ ∃ z, x + z = y :=
by
  intro x y
  constructor
  · intro h_xy
    obtain ⟨diff, hdiff⟩ := add_diff_exists M x y
    cases hdiff with
    | inl heq => exists diff
    | inr heq =>
      exists 0
      rw [B3]
      apply B7
      constructor
      · exact h_xy
      · rw [<- heq]
        apply B8
  · intro h
    obtain ⟨z, hz⟩ := h
    rw [<- hz]
    apply B8


-- D4. (x ≤ y ∧ y ≤ z) → x ≤ z  (Transitivity)
theorem le_trans :
  ∀ x y z : M, x ≤ y ∧ y ≤ z → x ≤ z :=
by sorry

-- D5. x ≤ y ∨ y ≤ x  (Total order)
theorem le_total :
  ∀ x y : M, x ≤ y ∨ y ≤ x :=
by sorry

-- D6. x ≤ y ↔ x + z ≤ y + z
theorem le_add_right :
  ∀ x y z : M, x ≤ y ↔ x + z ≤ y + z :=
by sorry

-- D7. x ≤ y → x * z ≤ y * z
theorem le_mul_right :
  ∀ x y z : M, x ≤ y → x * z ≤ y * z :=
by sorry

-- D8. x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1)  (Discreteness 1)
theorem le_succ_iff :
  ∀ x y : M, x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1) :=
by sorry

-- D9. x < y ↔ x + 1 ≤ y  (Discreteness 2)
-- recall: x < y means x ≤ y ∧ x ≠ y
theorem lt_iff_succ_le :
  ∀ x y : M, (x ≤ y ∧ x ≠ y) ↔ x + 1 ≤ y :=
by sorry

-- D10. x * z = y * z ∧ z ≠ 0 → x = y  (Cancellation law for ·)
theorem mul_cancel_right :
  ∀ x y z : M, (x * z = y * z ∧ z ≠ 0) → x = y :=
by sorry


-- D4 used
instance : PartialOrder M where
  le_refl := BASICModel.le_refl M
  le_trans := by
    intro a b c h_ab h_bc
    apply le_trans M
    constructor; exact h_ab; exact h_bc
  le_antisymm := by
    intro a b hab hba
    apply B7
    exact ⟨hab, hba⟩

-- D6 used
instance : IsOrderedAddMonoid M where
  add_le_add_left := fun a b h c ↦ by
    rw [IOPENModel.add_comm _ c, IOPENModel.add_comm _ c]
    exact (le_add_right M a b c).mp h

-- D7 used
instance : IsOrderedMonoid M where
  mul_le_mul_left := fun a b h c ↦ by
    rw [IOPENModel.mul_comm _ c, IOPENModel.mul_comm _ c]
    exact le_mul_right M a b c h

instance : AddCommMonoid M where


instance : IsOrderedRing M where
  zero_le_one := by exact IOPENModel.zero_le M 1
  mul_le_mul_of_nonneg_left := by
    intro a b c hab h_zero_c
    exact mul_le_mul_left' hab c
  mul_le_mul_of_nonneg_right := by
    exact fun a b c a_1 a_2 ↦ le_mul_right M a b c a_1

instance : CommSemiring M where

instance : IsStrictOrderedRing M where
  le_of_add_le_add_left := by



end IDelta0Model
