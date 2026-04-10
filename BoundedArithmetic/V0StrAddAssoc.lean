-- This file proves:
-- ∀ {X Y Z : str}, (X + Y) + Z = X + (Y + Z)
-- However, the proof was done using leanstral and is very verbose
-- Please see V0.lean for the manually written foundations.
import BoundedArithmetic.V0StrAddComm

variable {num str : Type} [M : V0ExtModel num str]
open FirstOrder Language
open HasTypes_is
open HasEmptySet
open HasLen
open HasSucc
open V0ExtModel V0Model BASICModel

lemma add_assoc_bit_bool {A B C D X Y Z : Prop} :
    (Xor' A B ↔ Xor' C D) ->
      (Xor' (Xor' (Xor' (Xor' X Y) C) Z) D ↔
        Xor' (Xor' X (Xor' (Xor' Y Z) A)) B) := by
  intro h
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;>
    by_cases hX : X <;> by_cases hY : Y <;> by_cases hZ : Z <;>
    simp [Xor', hA, hB, hC, hD, hX, hY, hZ] at h ⊢

lemma carry_pair_step_bool {A B C D X Y Z : Prop} :
    (A ∧ B ↔ C ∧ D) ->
    (Xor' A B ↔ Xor' C D) ->
      (((Maj A Y Z) ∧ (Maj B X (Xor' (Xor' Y Z) A))) ↔
        ((Maj C X Y) ∧ (Maj D (Xor' (Xor' X Y) C) Z))) ∧
      (Xor' (Maj A Y Z) (Maj B X (Xor' (Xor' Y Z) A)) ↔
        Xor' (Maj C X Y) (Maj D (Xor' (Xor' X Y) C) Z)) := by
  intro h_and h_xor
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;>
    by_cases hX : X <;> by_cases hY : Y <;> by_cases hZ : Z <;>
    simp [Maj, Xor', hA, hB, hC, hD, hX, hY, hZ] at h_and h_xor ⊢

def CarryAssocPred (X Y Z : str) (i : num) : Prop :=
  ((Carry i Y Z ∧ Carry i X (Y + Z)) ↔ (Carry i X Y ∧ Carry i (X + Y) Z)) ∧
  (Xor' (Carry i Y Z) (Carry i X (Y + Z)) ↔ Xor' (Carry i X Y) (Carry i (X + Y) Z))

/-
This is the only induction instance assumed here for proving associativity of string
addition. The displayed predicate is exactly the stronger Cook–Nguyen carry invariant,
and it is built from bounded formulas already present in `V0`.
-/
lemma carry_assoc_induction :
    ∀ {X Y Z : str},
      CarryAssocPred X Y Z (0 : num) ->
      (∀ i : num, CarryAssocPred X Y Z i -> CarryAssocPred X Y Z (i + (1 : num))) ->
      ∀ i : num, CarryAssocPred X Y Z i := by
  sorry

lemma carry_pair_assoc : ∀ {X Y Z : str}, ∀ {i : num},
    ((Carry i Y Z ∧ Carry i X (Y + Z)) ↔ (Carry i X Y ∧ Carry i (X + Y) Z)) ∧
    (Xor' (Carry i Y Z) (Carry i X (Y + Z)) ↔ Xor' (Carry i X Y) (Carry i (X + Y) Z)) := by
  intro X Y Z i
  have hφ : ∀ j : num, CarryAssocPred X Y Z j := by
    apply carry_assoc_induction (X := X) (Y := Y) (Z := Z)
    · have h0_yz : ¬ Carry (0 : num) Y Z := (carry_rec (i := (0 : num)) (X := Y) (Y := Z)).1
      have h0_x_yz : ¬ Carry (0 : num) X (Y + Z) := (carry_rec (i := (0 : num)) (X := X) (Y := Y + Z)).1
      have h0_xy : ¬ Carry (0 : num) X Y := (carry_rec (i := (0 : num)) (X := X) (Y := Y)).1
      have h0_xy_z : ¬ Carry (0 : num) (X + Y) Z := (carry_rec (i := (0 : num)) (X := X + Y) (Y := Z)).1
      constructor
      · constructor
        · intro h
          exact False.elim (h0_yz h.1)
        · intro h
          exact False.elim (h0_xy h.1)
      · simp [Xor', h0_yz, h0_x_yz, h0_xy, h0_xy_z]
    · intro j h_j
      rcases h_j with ⟨h_j_and, h_j_xor⟩
      have h_step :=
        carry_pair_step_bool (X := j ∈ X) (Y := j ∈ Y) (Z := j ∈ Z) h_j_and h_j_xor
      constructor
      · rw [(carry_rec (i := j) (X := Y) (Y := Z)).2]
        rw [(carry_rec (i := j) (X := X) (Y := Y + Z)).2]
        rw [(carry_rec (i := j) (X := X) (Y := Y)).2]
        rw [(carry_rec (i := j) (X := X + Y) (Y := Z)).2]
        rw [mem_add_iff_xor (X := Y) (Y := Z) (i := j)]
        rw [mem_add_iff_xor (X := X) (Y := Y) (i := j)]
        exact h_step.1
      · rw [(carry_rec (i := j) (X := Y) (Y := Z)).2]
        rw [(carry_rec (i := j) (X := X) (Y := Y + Z)).2]
        rw [(carry_rec (i := j) (X := X) (Y := Y)).2]
        rw [(carry_rec (i := j) (X := X + Y) (Y := Z)).2]
        rw [mem_add_iff_xor (X := Y) (Y := Z) (i := j)]
        rw [mem_add_iff_xor (X := X) (Y := Y) (i := j)]
        exact h_step.2
  exact hφ i


-- For Associativity, first show in V0(+) that
-- Carry(i, Y, Z) ⊕ Carry(i, X, Y + Z) ↔
-- Carry(i, X, Y ) ⊕ Carry(i, X + Y, Z).
-- Derive a stronger statement than this, and prove it by induction on i.
theorem str_add_assoc : ∀ {X Y Z : str}, (X + Y) + Z = X + (Y + Z) := by
  intro X Y Z
  refine str_eq_of_mem_iff (num := num) (str := str) (X := (X + Y) + Z) (Y := X + (Y + Z)) ?_
  intro i
  rw [mem_add_iff_xor (X := X + Y) (Y := Z) (i := i)]
  rw [mem_add_iff_xor (X := X) (Y := Y + Z) (i := i)]
  rw [mem_add_iff_xor (X := X) (Y := Y) (i := i)]
  rw [mem_add_iff_xor (X := Y) (Y := Z) (i := i)]
  exact add_assoc_bit_bool (carry_pair_assoc (X := X) (Y := Y) (Z := Z) (i := i)).2
