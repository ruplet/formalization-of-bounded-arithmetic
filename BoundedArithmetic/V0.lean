import Lean

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.SimpRw

import BoundedArithmetic.BasicSingleSorted
import BoundedArithmetic.IOPEN
import BoundedArithmetic.IDelta0
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.Complexity
import BoundedArithmetic.Algebra
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.Register


open FirstOrder Language
open HasTypes_is
open HasEmptySet
open HasLen


-- page 129, CN10: Finite axiomatizability of V0
class V0Model
  (num : Type) (str : outParam Type)
  extends
  HasLen str num,
  Membership num str,
  IDelta0Model num
where
  -- axiom for empty string; 4.4.1 Two-Sorted Free Variable Normal Form
  -- E : len (empty : str) = (0 : num)
  -- B1 : ∀ x : num,       x + 1 ≠ 0
  -- B2 : ∀ x y : num, x + 1 = y + 1 -> x = y
  -- B3 : ∀ x : num,       x + 0 = x
  -- B4 : ∀ x y : num, x + (y + 1) = (x + y) + 1
  -- B5 : ∀ x : num,       x * 0 = 0
  -- B6 : ∀x y : num, x * (y + 1) = (x * y) + x
  -- B7 : ∀x y : num, x <= y -> y <= x -> x = y
  -- B8 : ∀x y : num, x <= x + y
  B9 : ∀ x : num,       0 <= x
  B10: ∀ x y : num, x <= y ∨ y <= x
  B11: ∀ x y : num, x <= y <-> x < (y + 1)
  B12: ∀ {x : num},       x ≠ 0 -> (∃ y : num, (y <= x ∧ (y + 1) = x))
  L1 : ∀ {X : str}, ∀ {y : num}, y ∈ X -> (y <= (len X) ∧ y ≠ (len X))
  L2 : ∀ {X : str}, ∀ {y : num}, (y + 1) = len X -> y ∈ X

  SE : ∀ {X Y: str},
    len X = (len Y : num)
    -> (∀ y : num, ((y < len X) -> (y ∈ X <-> y ∈ Y)))
    -> X = Y

  comp1 : ∀ b1 b2 : num, ∃ Y : str, (len Y ≤ ⟨b1, b2⟩ ∧ (∀ x1 < b1, ∀ x2 < b2,
    ⟨x1, x2⟩ ∈ Y ↔ (x1 = x2)
  ))

  -- φ2(x1,x2,x3) ≡ x3 = x1
  comp2 : ∀ b1 b2 b3 : num, ∃ Y : str, len Y ≤ ⟨b1, b2, b3⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2, ∀ x3 < b3,
      ⟨x1, x2, x3⟩ ∈ Y ↔ (x3 = x1)

  -- φ3(x1,x2,x3) ≡ x3 = x2
  comp3 : ∀ b1 b2 b3 : num, ∃ Y : str, len Y ≤ ⟨b1, b2, b3⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2, ∀ x3 < b3,
      ⟨x1, x2, x3⟩ ∈ Y ↔ (x3 = x2)

  -- φ4[Q1,Q2](x1,x2) ≡ ∃y ≤ x1 (Q1(x1,y) ∧ Q2(y,x2))
  comp4 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2,
      ⟨x1, x2⟩ ∈ Y ↔ (∃ y : num, y ≤ x1 ∧ (⟨x1, y⟩ ∈ Q1 ∧ ⟨y, x2⟩ ∈ Q2))

  -- φ5[a](x,y) ≡ y = a
  comp5 : ∀ a : num, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔ (y = a)

  -- φ6[Q1,Q2](x,y) ≡ ∃z1 ≤ y ∃z2 ≤ y (Q1(x,z1) ∧ Q2(x,z2) ∧ y = z1 + z2)
  comp6 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔
        (∃ z1 : num, z1 ≤ y ∧
         ∃ z2 : num, z2 ≤ y ∧
           (⟨x, z1⟩ ∈ Q1 ∧ ⟨x, z2⟩ ∈ Q2 ∧ y = z1 + z2))

  -- φ7[Q1,Q2](x,y) ≡ ∃z1 ≤ y ∃z2 ≤ y (Q1(x,z1) ∧ Q2(x,z2) ∧ y = z1 · z2)
  comp7 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔
        (∃ z1 : num, z1 ≤ y ∧
         ∃ z2 : num, z2 ≤ y ∧
           (⟨x, z1⟩ ∈ Q1 ∧ ⟨x, z2⟩ ∈ Q2 ∧ y = z1 * z2))

  -- φ8[Q1,Q2,c](x) ≡ ∃y1 ≤ c ∃y2 ≤ c (Q1(x,y1) ∧ Q2(x,y2) ∧ y1 ≤ y2)
  comp8 : ∀ Q1 Q2 : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔
        (∃ y1 : num, y1 ≤ c ∧
         ∃ y2 : num, y2 ≤ c ∧
           (⟨x, y1⟩ ∈ Q1 ∧ ⟨x, y2⟩ ∈ Q2 ∧ y1 ≤ y2))

  -- φ9[X,Q,c](x) ≡ ∃y ≤ c (Q(x,y) ∧ X(y))
  comp9 : ∀ X Q : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (∃ y : num, y ≤ c ∧ (⟨x, y⟩ ∈ Q ∧ y ∈ X))

  -- φ10[Q](x) ≡ ¬Q(x)
  comp10 : ∀ Q : str, ∀ b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ ¬ (x ∈ Q)

  -- φ11[Q1,Q2](x) ≡ Q1(x) ∧ Q2(x)
  comp11 : ∀ Q1 Q2 : str, ∀ b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (x ∈ Q1 ∧ x ∈ Q2)

  -- φ12[Q,c](x) ≡ ∀y ≤ c Q(x,y)
  comp12 : ∀ Q : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (∀ y : num, y ≤ c → ⟨x, y⟩ ∈ Q)

variable {num str} [M : V0Model.{0, 0} num str]
open V0Model


theorem xmin_comp (X : str) : ∃ Y : str, (len Y : num) ≤ len X ∧ ∀ z < len X, z ∈ Y ↔ ∀ y ≤ z, y ∉ X :=
by
  sorry

lemma ex_elt_of_len_pos : ∀ {X : str}, (0 : num) < (len X) -> ∃ x, x ∈ X ∧ x + 1 = len X := by
  intro X h_len
  obtain ⟨len_pred, h_le, h_eq⟩ := M.B12 h_len.right.symm
  exists len_pred
  constructor
  · apply L2
    exact h_eq
  · exact h_eq

lemma lt_succ : ∀ (x : num), x < x + 1 := by
  intro x
  constructor
  · apply M.B8
  · intro h
    conv at h => lhs; rw [<- add_zero x]
    rw [add_left_cancel_iff] at h
    apply M.B1 0
    symm
    rw [<- h]
    rw [@right_eq_add]

lemma len_not_in : ∀ {X : str}, len X ∉ X := by
  intro X h
  apply (L1 h).right
  rfl

-- Exercise V.1.1
lemma not_lt_zero
  : ∀ {x : num}, ¬ x < 0 :=
by
  intro x
  rw [not_lt_iff_eq_or_lt]
  exact eq_zero_or_pos x

instance : CanonicallyOrderedAdd num where
  le_self_add := by
    intro a b
    conv => lhs; rw [<- M.B3 a]
    apply add_le_add
    · apply le_refl
    · apply M.B9

theorem xmin :
  ∀ {X : str}, (0 : num) < len X -> ∃ x < len X, x ∈ X ∧ ∀ y < x, y ∉ X :=
by
  intro X h_lenX
  obtain ⟨Y, h_Y⟩ := xmin_comp X (num := num)
  exists (len Y)
  by_cases h : (0 : num) < len Y
  · obtain ⟨y, hy_in, hy_eq⟩ := ex_elt_of_len_pos h
    constructor
    · -- len Y < len X
      cases le_iff_eq_or_lt.mp h_Y.left with
      | inl h_lenY_eq_lenX =>
        exfalso
        have h_X_empty : ∀ x < len X, x ∉ X := by
          have aux := h_Y.right y
          rw [<- h_lenY_eq_lenX] at aux
          specialize aux (L1 hy_in)
          intro x h_x_lt
          apply aux.mp hy_in
          rw [B11, hy_eq]
          rw [h_lenY_eq_lenX]
          exact h_x_lt

        have h_X_empty' : ¬∃ x < len X, x ∈ X := by
          refine not_exists_of_forall_not ?_
          intro x hx
          apply h_X_empty x hx.left hx.right

        apply h_X_empty'
        obtain ⟨wit, h_wit⟩ := ex_elt_of_len_pos (X := X) (by
          rw [h_lenY_eq_lenX] at h
          exact h
        )

        exists wit
        constructor
        apply L1 h_wit.left
        exact h_wit.left
      | inr h_lenY_lt_lenX =>
        assumption
    · constructor
      · -- len Y ∈ X
        rw [le_iff_eq_or_lt] at h_Y
        cases h_Y.left with
        | inl h =>
          exfalso
          rw [<- h] at h_lenX
          conv at h_Y => right; rw [<- h]
          have aux := (h_Y.right y (M.L1 hy_in)).mp hy_in y (le_refl _)
          apply aux
          apply L2
          rw [<- h]
          exact hy_eq
        | inr h =>
          have aux := (not_congr $ h_Y.right (len Y) h).mp len_not_in
          simp only [not_forall, not_not] at aux
          obtain ⟨x, h_x_le, h_x_X⟩ := aux
          rw [le_iff_eq_or_lt] at h_x_le
          cases h_x_le with
          | inl h =>
            rw [<- h]
            exact h_x_X
          | inr h =>
            -- first, obtain hypothesis for last y of Y
            have len_Y_ne_zero : (len Y : num) ≠ 0 := by
              intro h'
              rw [h'] at h
              apply not_lt_zero h
            have len_Y_pos : 0 < (len Y : num) := by
              cases (eq_zero_or_pos (len Y : num)) with
              | inl h =>
                exfalso
                apply len_Y_ne_zero
                exact h
              | inr h =>
                exact h
            obtain ⟨y, hy_in, hy_eq⟩ := ex_elt_of_len_pos len_Y_pos
            clear len_Y_ne_zero len_Y_pos h_lenX

            rename_i h_lenY_lt_lenX
            have h_y_lt_lenX : y < (len X) := by
              apply lt_trans _ h_lenY_lt_lenX
              apply L1 hy_in

            -- then show that if last of Y holds, but (len Y) does not,
            -- then some bit had to be set in X
            false_or_by_contra
            · rename_i h_lenY_notin_X
              have h := (h_Y.right (len Y) h_lenY_lt_lenX).mpr
              apply @len_not_in num _ _ Y
              apply h
              intro y2 h_y2
              rw [le_iff_eq_or_lt] at h_y2
              cases h_y2 with
              | inl h_y2 =>
                rw [h_y2]
                apply (h_Y.right (len Y) h_lenY_lt_lenX).mp
                apply h
                intro y3 hy3
                rw [le_iff_eq_or_lt] at hy3
                cases hy3 with
                | inl hy3 =>
                  rw [hy3]
                  exact h_lenY_notin_X
                | inr hy3 =>
                  apply (h_Y.right y h_y_lt_lenX).mp hy_in
                  rw [B11, hy_eq]
                  exact hy3
                rfl
              | inr h_y2 =>
                clear h
                apply (h_Y.right y h_y_lt_lenX).mp hy_in
                rw [B11, hy_eq]
                exact h_y2
      · -- ∀ z < len Y, z ∉ X
        intro z h_z
        intro h_zX
        -- notice: Y is of the form 11111..1 - if we get any 0 in Y,
        -- it means that a bit in X was set. so, we won't get any further
        -- bits set in Y!
        have h_y_lt_lenX : y < len X := by
          apply lt_of_lt_of_le (L1 hy_in) h_Y.left

        have h_X := (h_Y.right y h_y_lt_lenX).mp hy_in z
        apply h_X
        · rw [B11, hy_eq]
          exact h_z
        · exact h_zX
  · have Y_empty : len Y = (0 : num) := by
      have h1 := B9 (num := num) (len Y)
      rw [le_iff_eq_or_lt] at h1
      cases h1 with
      | inl h1 => exact h1.symm
      | inr h1 => exfalso; apply h; exact h1
    constructor
    · rw [Y_empty]
      exact h_lenX
    · constructor
      · -- len Y ∈ X
        false_or_by_contra
        rename_i h_contr
        have zero_in_Y : (0 : num) ∈ Y := by
          apply (h_Y.right 0 h_lenX).mpr
          intro y hy
          have y_zero := M.B7 _ _ hy (M.B9 _)
          rw [y_zero, <- Y_empty]
          exact h_contr
        rw [<- Y_empty] at zero_in_Y
        exact len_not_in zero_in_Y
      · -- ∀ y < len Y, y ∉ X
        intro y hy
        exfalso
        rw [Y_empty] at hy
        exact not_lt_zero hy


-- variable {num} {str : outParam Type} [V0Model num str]


class HasSucc.{u} (α : Type u) where
  succ : α -> α

def Carry {num str} [V0Model num str] (i : num) (X Y : str) := ∃ k < i, (k ∈ X ∧ k ∈ Y ∧ ∀ j < i, (k < j → (j ∈ X ∨ j ∈ Y)))

class V0ExtModel
  (num : Type) (str : outParam Type)
  extends
  Zero str, HasSucc str, Add str,
  V0Model (num := num) (str := str)
where
  ax_empty : ∀ {z : num}, z ∈ (0 : str) ↔ z < 0
  ax_succ : ∀ {X : str}, ∀ {i : num}, i ∈ HasSucc.succ X ↔
    (i ≤ len X
      ∧ ((i ∈ X ∧ ∃ j < i, j ∉ X)
          ∨ (i ∉ X ∧ ∀ j < i, j ∈ X)
        )
    )

  ax_add : ∀ {X Y : str}, ∀ {i : num}, i ∈ X + Y ↔
    (i < len X + len Y ∧ (Xor' (Xor' (i ∈ X) (i ∈ Y)) (Carry i X Y)))

-- Exercise V.4.19

-- namespace V0ExtModel
variable [M : V0ExtModel.{0, 0} num str]

open V0ExtModel V0Model BASICModel


lemma len_empty : len (0 : str) = (0 : num) := by
  false_or_by_contra
  rename_i h
  obtain ⟨pred, pred_le, pred_eq⟩ := B12 (num := num) h
  have witness := L2 pred_eq
  have aux := @ax_empty.{0, 0} _ _ _ pred
  apply @not_lt_zero _ _ _ pred
  apply aux.mp

lemma ax_empty' : ∀ {z : num}, z ∉ (0 : str) := by
  intro z
  rw [ax_empty]
  exact not_lt_zero

lemma not_carry_empty : ∀ {X : str}, ∀ {i : num}, ¬Carry i X 0 := by
  intro X i h
  obtain ⟨_, _, _, bad, _⟩ := h
  exact ax_empty' bad

def Maj (P Q R : Prop) := P ∧ Q ∨ Q ∧ R ∨ P ∧ R

open IDelta0Model

lemma carry_rec1 : ∀ {X Y : str}, ∀ {i : num},
  Carry i X Y -> (i ∈ X ∨ i ∈ Y) -> Carry (i + 1) X Y :=
by
  intro X Y i h ixy
  obtain ⟨c, c_lt, cx, cy, cprev⟩ := h
  exists c
  constructor; rw [<- B11]; exact c_lt.1
  constructor; exact cx
  constructor; exact cy
  intro j
  by_cases j = i
  · rename_i hji
    intro _ hcj
    rw [hji]
    cases ixy with
    | inl ix => left; exact ix
    | inr iy => right; exact iy
  · rename_i hji
    intro hlt hcj
    apply cprev
    apply lt_of_le_of_ne
    rw [B11]; exact hlt
    exact hji
    exact hcj


-- Exercise V.4.18
lemma carry_rec : ∀ {X Y : str}, ∀ {i : num},
  (¬ Carry (0 : num) X Y) ∧ (Carry (i + 1) X Y ↔ Maj (Carry i X Y) (i ∈ X) (i ∈ Y)) := by
  intro X Y i
  constructor
  · intro h
    obtain ⟨_, lt, _⟩ := h
    exact not_lt_zero lt
  · constructor
    · intro h
      obtain ⟨pos, lt, inX, inY, prevs⟩ := h
      by_cases h_pos : i = pos
      · rw [h_pos]
        right; left; constructor <;> assumption
      · rw [<- B11] at lt
        have hlt : pos < i := lt_of_le_of_ne lt (Ne.symm h_pos)
        clear h_pos lt
        have h_pos := prevs i (by rw [<- B11]) hlt
        unfold Maj
        suffices demorgan : (Carry i X Y ∧ (i ∈ X ∨ i ∈ Y))
        · cases demorgan.2 with
          | inl =>
            left; constructor; exact demorgan.1; assumption
          | inr =>
            right; right; constructor; exact demorgan.1; assumption
        · symm; constructor; exact h_pos
          exists pos
          constructor; exact hlt
          constructor; exact inX
          constructor; exact inY
          intro j hj; apply prevs j
          apply lt_trans hj
          rw [<- B11]
    · intro h
      cases h with
      | inl h =>
        refine carry_rec1 h.1 (.inl h.2)
      | inr h =>
        cases h with
        | inl h =>
          exists i
          constructor; rw [<- B11]
          constructor; exact h.1
          constructor; exact h.2
          intro j hj hij
          exfalso
          have h := lt_iff_succ_le.mp hij
          have h2 := B7 _ _ h hj.1
          apply hj.2
          exact h2.symm
        | inr h =>
          refine carry_rec1 h.1 (.inr h.2)

lemma exists_of_len_lt : ∀ {X Y : str}, (len X : num) < len Y -> ∃ z, z ∈ Y ∧ z ∉ X ∧ z + 1 = len Y := by
  intro X Y h_lt
  have h_len_ne_zero := ne_zero_of_lt h_lt (α := num)
  obtain ⟨len_pred, pred_le, pred_eq⟩ := B12 (num := num) h_len_ne_zero
  have pred_in := L2 pred_eq
  rw [lt_iff_le_not_ge] at h_lt
  exists len_pred
  constructor
  exact pred_in
  symm
  constructor
  exact pred_eq
  intro h_in_X
  apply h_lt.2
  rw [B11]
  rw [<- pred_eq]
  rw [add_lt_add_iff_right]
  apply L1
  exact h_in_X

lemma exists_of_len_lt' : ∀ {X : str}, ∀ {i : num}, i < len X -> ∃ z, z ∈ X ∧ i ≤ z ∧ z + 1 = len X := by
  intro X i h_lt
  have h_len_ne_zero := ne_zero_of_lt h_lt (α := num)
  obtain ⟨len_pred, pred_le, pred_eq⟩ := B12 (num := num) h_len_ne_zero
  have pred_in := L2 pred_eq
  rw [lt_iff_le_not_ge] at h_lt
  exists len_pred
  constructor
  exact pred_in
  symm
  constructor
  exact pred_eq
  rw [B11]
  rw [pred_eq]
  constructor
  exact h_lt.1
  intro h
  apply h_lt.2
  exact _root_.le_of_eq h.symm

lemma len_add_empty : ∀ X : str, len (X + 0) = (len X : num) := by
  false_or_by_contra
  rename_i hlen
  cases lt_or_gt_of_ne hlen with
  | inl hlen =>
    obtain ⟨k, k_in, k_notin, k_eq⟩ := exists_of_len_lt hlen
    apply k_notin
    rw [ax_add]
    constructor
    · rw [len_empty]
      rw [B3]
      rw [<- k_eq]
      rw [<- B11]
    · constructor
      constructor
      · constructor
        constructor
        · exact k_in
        · exact ax_empty'
      · exact not_carry_empty
  | inr hlen =>
    obtain ⟨k, k_in, k_notin, k_eq⟩ := exists_of_len_lt hlen
    apply k_notin
    rw [ax_add] at k_in
    obtain ⟨_, h_carry⟩ := k_in
    cases h_carry with
    | inl h_carry =>
      obtain ⟨h_carry_len, _⟩ := h_carry
      cases h_carry_len with
      | inl h_carry =>
        exact h_carry.1
      | inr h_carry =>
        exfalso
        exact ax_empty' h_carry.1
    | inr h_carry =>
      exfalso
      exact not_carry_empty h_carry.1

theorem str_add_zero : ∀ X : str, X + (0 : str) = X := by
  intro X
  apply M.SE
  · apply len_add_empty
  · intro y h_ylen
    constructor
    · intro hy
      false_or_by_contra
      rename_i h
      apply h
      rw [ax_add] at hy
      obtain ⟨_, h_xor⟩ := hy
      cases h_xor with
      | inl h_xor =>
        cases h_xor.1 with
        | inl h_xor =>
          exact h_xor.1
        | inr h_xor =>
          exfalso
          exact ax_empty' h_xor.1
      | inr h_xor =>
        obtain ⟨_, _, _, bad, _⟩ := h_xor.1
        exfalso; exact ax_empty' bad
    · intro hy
      rw [ax_add]
      constructor
      · rw [len_empty]
        rw [add_zero]
        rw [len_add_empty] at h_ylen
        exact h_ylen
      · constructor; constructor
        · constructor; constructor
          · exact hy
          · exact ax_empty'
        · intro h_bad
          apply not_carry_empty h_bad

open HasSucc

lemma len_le_len_succ : ∀ {X : str}, (len X : num) ≤ len (succ X) := by
  intro X
  false_or_by_contra
  rename_i h
  rw [not_le] at h
  obtain ⟨p, px, ps, p_eq⟩ := exists_of_len_lt h
  rw [ax_succ] at ps
  simp only [not_and, not_or, not_exists, not_not, not_forall] at ps
  specialize ps (by
    rw [<- p_eq]
    exact le_self_add
  )
  have aux : (p + 1) ∈ succ X := by
    rw [ax_succ]
    constructor
    rw [p_eq]
    right
    constructor
    intro hp
    apply (L1 _ _ hp).2
    exact p_eq
    intro j jp
    by_cases hj : j = p
    · rw [hj]; exact px
    · apply ps.1
      exact px
      constructor
      rw [B11]
      exact jp
      exact hj

  have aux2 : p + 1 ≤ len (succ X) := (L1 _ _ aux).1
  rw [p_eq] at aux2
  have aux3 : len X < len X := lt_of_le_of_lt aux2 h
  apply aux3.2
  rfl


lemma len_add_le_add_len : ∀ {X Y : str}, len (X + Y) ≤ (len X : num) + len Y := by
  intro X Y
  by_cases len (X + Y) = (0 : num)
  · (expose_names; exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) h (len X + len Y))
  · rename_i h
    obtain ⟨k, k_le, k_eq⟩ := B12 h
    have last := L2 k_eq
    rw [ax_add] at last
    rw [<- k_eq]
    rw [B11]
    rw [@add_lt_add_iff_right]
    exact last.1

lemma mem_succ_iff_xor_prefix :
    ∀ {Z : str} {i : num},
      i ∈ succ Z ↔ i ≤ len Z ∧ Xor' (i ∈ Z) (∀ j < i, j ∈ Z) := by
  intro Z i
  classical
  constructor
  · intro hi
    have h := (ax_succ (X := Z) (i := i)).1 hi
    rcases h with ⟨h_le, h_cases⟩
    refine ⟨h_le, ?_⟩
    cases h_cases with
    | inl h1 =>
        rcases h1 with ⟨hiZ, ⟨j, hjlt, hjnot⟩⟩
        left
        refine ⟨hiZ, ?_⟩
        intro hall
        exact hjnot (hall j hjlt)
    | inr h2 =>
        rcases h2 with ⟨hiZ, hall⟩
        right
        symm
        exact ⟨hiZ, hall⟩
  · rintro ⟨h_le, hxor⟩
    have h_cases :
        (i ∈ Z ∧ ∃ j < i, j ∉ Z) ∨ (i ∉ Z ∧ ∀ j < i, j ∈ Z) := by
      cases hxor with
      | inl h =>
          rcases h with ⟨hiZ, hnall⟩
          left
          refine ⟨hiZ, ?_⟩
          by_contra hno
          have hall : ∀ j < i, j ∈ Z := by
            intro j hjlt
            by_contra hjnot
            exact hno ⟨j, hjlt, hjnot⟩
          exact hnall hall
      | inr h =>
          right
          symm
          exact h
    exact (ax_succ (X := Z) (i := i)).2 ⟨h_le, h_cases⟩

lemma prefix_carry_lemma :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ (X + Y)) ↔
        Xor' (∀ j < i, j ∈ Y) (Xor' (Carry i X Y) (Carry i X (succ Y))) := by
  sorry

lemma add_succ_of_succ_add : ∀ {X Y : str}, ∀ {y : num}, y ∈ succ (X + Y) -> y ∈ X + succ Y := by
  intro X Y y hy


  rw [ax_succ] at hy
  obtain ⟨y_le, y_cond⟩ := hy
  cases y_cond with
  | inl y_cond =>
    rw [ax_add] at y_cond
    obtain ⟨⟨y_lt, y_xor⟩, y_prefix⟩ := y_cond
    cases y_xor with
    | inl y_xor =>
      obtain ⟨h_xy, not_carry⟩ := y_xor
      cases h_xy with
      | inl h_x =>


  rw [ax_add]
  constructor
  · sorry






lemma succ_len_eq : ∀ {X Y : str}, len (X + succ Y) = (len (succ (X + Y)) : num) := by
  intro X Y
  sorry


lemma succ_add_of_add_succ : ∀ {X Y : str}, ∀ {y : num}, y ∈ X + succ Y -> y ∈ succ (X + Y) := by
  sorry

lemma gt_iff_not_le : ∀ {x y : num}, ¬ x ≤ y <-> x > y := by
  intro x y
  constructor
  · simp only [not_le, gt_iff_lt, imp_self]
  · exact fun a ↦ not_le_of_gt a


lemma succ_add_iff_add_succ : ∀ {X Y : str}, ∀ {y : num}, y ∈ X + succ Y <-> y ∈ succ (X + Y) :=
  ⟨succ_add_of_add_succ, add_succ_of_succ_add⟩

theorem str_succ_assoc : ∀ {X Y : str}, X + succ Y = succ (X + Y) := by
  intro X Y
  apply M.SE
  · exact succ_len_eq
  · intro y y_lt
    exact succ_add_iff_add_succ
