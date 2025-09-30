import Mathlib.Algebra.Ring.Defs

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.Complexity
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
    exact B8 a 1
    -- exists a
    -- constructor
    -- · exact B8 a 1
    -- · exact rfl
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
        · right
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
by
  intro x y z h
  obtain ⟨hxy, hyz⟩ := h
  rw [le_iff_exists_add] at hxy hyz ⊢
  obtain ⟨diff_x_y, hdiff_x_y⟩ := hxy
  obtain ⟨diff_y_z, hdiff_y_z⟩ := hyz
  exists (diff_x_y + diff_y_z)
  rw [<- add_assoc]
  rw [hdiff_x_y]
  rw [hdiff_y_z]

-- D5. x ≤ y ∨ y ≤ x  (Total order)
theorem le_total :
  ∀ x y : M, x ≤ y ∨ y ≤ x :=
by
  intro x y
  obtain ⟨diff, hdiff⟩ := add_diff_exists M x y
  cases hdiff with
  | inl h =>
    left
    rw [le_iff_exists_add]
    exists diff
  | inr h =>
    right
    rw [le_iff_exists_add]
    exists diff

-- D6. x ≤ y ↔ x + z ≤ y + z
theorem le_add_right :
  ∀ x y z : M, x ≤ y ↔ x + z ≤ y + z :=
by
  intro x y z
  constructor
  · intro hxy
    rw [le_iff_exists_add] at hxy ⊢
    obtain ⟨diff, hdiff⟩ := hxy
    exists diff
    rw [<- add_rotate]
    rw [add_comm] at ⊢ hdiff
    rw [hdiff]
    rw [add_comm]
  · rw [le_iff_exists_add]
    rw [le_iff_exists_add]
    intro h
    obtain ⟨a, ha⟩ := h
    exists a
    apply add_cancel_right.mp
    conv at ha => rw [add_assoc]; lhs; rhs; rw [add_comm]
    rw [add_assoc]
    exact ha

theorem le_cancel_left :
  ∀ x y z : M, x <= y -> z + x <= z + y :=
by
  conv => rhs;rhs;rhs;rhs; rw[add_comm]; rhs; rw[add_comm]
  exact fun a a_3 a_4 a_5 ↦
    (fun M [IDelta0Model M] x y z ↦ (le_add_right M x y z).mp) M a a_3 a_4 a_5

-- D7. x ≤ y → x * z ≤ y * z
theorem le_mul_right :
  ∀ x y z : M, x ≤ y → x * z ≤ y * z :=
by
  intro x y z hxy
  rw [le_iff_exists_add] at hxy ⊢
  obtain ⟨diff, hdiff⟩ := hxy
  rw [<- hdiff]
  rw [add_mul]
  exists (diff * z)

-- D8. x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1)  (Discreteness 1)
theorem le_succ_iff :
  ∀ x y : M, x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1) :=
by
  intro x y
  constructor
  · intro hxy
    rw [le_iff_exists_add] at hxy
    obtain ⟨diff, hdiff⟩ := hxy
    by_cases h : diff = 0
    · rw [h] at hdiff
      right
      rw [B3] at hdiff
      exact hdiff
    · obtain ⟨pred_diff, hpred_diff_le, hpred_diff_eq⟩
        := pred_exists M diff h
      left
      rw [hpred_diff_eq] at hdiff
      rw [<- add_assoc] at hdiff
      rw [le_iff_exists_add]
      exists pred_diff
      apply add_right_cancel
      exact hdiff
  · intro h
    cases h with
    | inl h =>
      rw [le_iff_exists_add] at h ⊢
      rcases h with ⟨diff, hdiff⟩
      refine ⟨diff + 1, ?_⟩
      rw [<- add_assoc]
      rw [hdiff]
    | inr h =>
      rw [h]
      exact BASICModel.le_refl M (y + 1)

theorem le_of_eq :
  ∀ x y : M, x = y -> x ≤ y :=
by
  intro x y hxy
  rw [hxy]
  apply le_refl M

theorem lt_of_not_ge :
  ∀ x y : M, ¬ x <= y -> y < x :=
by
  intro x y h
  constructor
  · cases le_total M x y with
    | inl x_le =>
      contradiction
    | inr y_le =>
      exact y_le
  · intro h_eq
    apply h
    apply le_of_eq
    apply Eq.symm
    exact h_eq

theorem zero_if_sum_zero :
  ∀ x y : M, x + y = 0 -> x = 0 ∧ y = 0 :=
by
  intro x y h
  constructor
  · apply le_zero_eq
    have t := B8 x y
    rw [h] at t
    exact t
  · apply le_zero_eq
    have t := B8 y x
    rw [add_comm] at t
    rw [h] at t
    exact t

theorem lt_one_eq_zero :
  ∀ x : M, x < 1 -> x = 0 :=
by
  intro x hx
  rcases hx with ⟨h_x_le, h_x_neq⟩
  rw [le_iff_exists_add] at h_x_le
  rcases h_x_le with ⟨diff, hdiff⟩
  by_cases h : x = 0
  · trivial
  · obtain ⟨pred, hp1, hp2⟩ := pred_exists M x h
    rw [hp2] at hdiff
    rw [add_assoc] at hdiff
    conv at hdiff => lhs; rhs; rw [add_comm]
    rw [<- add_assoc] at hdiff
    conv at hdiff => rhs; rw [<- C]
    have hdiff := add_cancel_right.mp M (pred + diff) 0 1 hdiff
    have pred_zero := (zero_if_sum_zero M pred diff hdiff).left
    rw [pred_zero, C] at hp2
    exfalso
    apply h_x_neq
    exact hp2

-- D9. x < y ↔ x + 1 ≤ y  (Discreteness 2)
-- recall: x < y means x ≤ y ∧ x ≠ y
theorem lt_iff_succ_le :
  ∀ x y : M, (x ≤ y ∧ x ≠ y) ↔ x + 1 ≤ y :=
by
  intro x y
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    rw [le_iff_exists_add] at h1
    obtain ⟨diff, hdiff⟩ := h1
    rw [<- hdiff]
    apply le_cancel_left

    by_contra not_one_le_diff
    apply h2
    rw [<- hdiff]
    conv => lhs; rw [<- B3 x]
    rw [add_cancel_left M _ _ x]
    have diff_lt_one := lt_of_not_ge M 1 diff not_one_le_diff
    apply Eq.symm
    apply lt_one_eq_zero M diff diff_lt_one
  · rw [le_iff_exists_add]
    rw [le_iff_exists_add]
    intro h
    rcases h with ⟨diff, hdiff⟩
    constructor
    · exists (1 + diff)
      rw [<- add_assoc]
      exact hdiff
    · rw [<- hdiff]
      intro absurd
      conv at absurd => lhs; rw [<- B3 x]
      conv at absurd => rhs; rw [add_assoc]
      rw [add_cancel_left] at absurd
      apply B1 diff
      rw [add_comm]
      apply Eq.symm
      exact absurd

theorem mul_eq_zero_iff_left :
  ∀ x y : M, x ≠ 0 -> (x * y = 0 ↔ y = 0) :=
by
  intro x y hx
  constructor
  · intro hxy
    rcases pred_exists M x hx with ⟨xp, _, hxp_eq⟩
    rw [hxp_eq] at hxy
    rw [add_mul] at hxy
    by_contra hy
    rcases pred_exists M y hy with ⟨yp, _, hyp_eq⟩
    rw [hyp_eq] at hxy
    conv at hxy => lhs; rhs; rw [mul_add]
    rw [mul_one] at hxy
    rw [<- add_assoc] at hxy
    apply B1 (num := M)
    exact hxy
  · intro hy
    rw [hy]
    exact mul_zero x

-- D10. x * z = y * z ∧ z ≠ 0 → x = y  (Cancellation law for ·)
theorem mul_cancel_right :
  ∀ x y z : M, (x * z = y * z ∧ z ≠ 0) → x = y :=
by
  let ind1 : peano.Formula Vars3 := ((x * z) =' (y * z) ⊓ (z ≠' 0)) ⟹ (x =' y)
  let ind2 := display_x_xyz $ ind1
  let ind := delta0_induction (self := idelta0) ind2

  unfold ind2 ind1 at ind
  unfold display_x_xyz at ind
  rw [<- IsDelta0.relabelEquiv] at ind
  conv at ind =>
    rhs;
    unfold iBdEx' Term.neq
    simp [delta0_simps]

  intro x y z
  rw [and_imp]
  apply ind
  -- prove IsDelta0
  · constructor
    · rw [IsDelta0.min]
      constructor
      · apply IsDelta0.equal
      · apply IsDelta0.neq
    · apply IsDelta0.equal
  · intro y z hyz hz
    by_cases hy : y = 0
    · exact hy.symm
    · rcases pred_exists M y hy with ⟨yp, _, hyp_eq⟩
      rcases pred_exists M z hz with ⟨zp, _, hzp_eq⟩
      rw [hyp_eq, hzp_eq] at hyz
      rw [mul_add] at hyz
      rw [mul_one] at hyz
      rw [<- add_assoc] at hyz
      exfalso
      apply B1 $ (yp + 1) * zp + yp
      apply Eq.symm
      exact hyz
  · intro y hind x z hass hz
    -- hind tells us that we can right-cancel
    -- multiplication by `a_1` if the other factor at RHS is `a`

    -- right-cancel multiplication by `z` in `hass`
    have hx : x ≠ 0 := by
      by_contra hx
      rw [hx] at hass
      rw [zero_mul] at hass
      rw [mul_eq_zero_iff_left] at hass
      apply hz
      exact hass
      exact B1 y
    rcases pred_exists M x hx with ⟨xp, _, hxp_eq⟩
    rw [hxp_eq] at hass
    rw [add_mul] at hass
    rw [add_mul] at hass
    rw [one_mul] at hass
    rw [add_cancel_right] at hass
    specialize hind xp z

    -- match induction result and the goal
    conv at hind =>
      rhs; rhs; rw [<- @add_cancel_right _ _ _ _ 1]
    rw [hxp_eq]

    apply hind
    · exact hass
    · exact hz

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
    exact hab
    exact hba
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

noncomputable instance : LinearOrder M where
  le_total := le_total M
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
      apply zero_le M b
    else
      if hb : b = 0 then
        apply Decidable.isFalse
        rw [hb]
        intro ha'
        apply ha
        exact le_zero_eq M a ha'
      else
        -- HERE, WE SHOULD TAKE PREDECESSOR OF
        -- BOTH AND RECURSE!
        exact Classical.propDecidable (a ≤ b)


-- instance : IsStrictOrderedRing M where
--   le_of_add_le_add_left := by
--     intro a b c h
--     rw [le_cancel_left]


end IDelta0Model
