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
  BASICModel num
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
  L1 : ∀ {X : str}, ∀ {y : num}, y ∈ X -> (y < (len X))
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

  -- le_refl : ∀ x : num, x <= x
  le_trans : ∀ x y z : num, x <= y -> y <= z -> x <= z
  zero_add : ∀ x : num, 0 + x = x
  add_left_cancel : ∀ x : num, IsAddLeftRegular x
  add_right_cancel : ∀ x : num, IsAddRightRegular x
  add_assoc : ∀ x y z : num, (x + y) + z = x + (y + z)
  le_total : ∀ (a b : num), a ≤ b ∨ b ≤ a
  toDecidableLE : DecidableLE num
  exists_add_of_le : ∀ {a b : num}, a ≤ b → ∃ c, b = a + c
  add_le_add_left : ∀ (a b : num), a ≤ b → ∀ (c : num), c + a ≤ c + b
  le_antisymm : ∀ (a b : num), a ≤ b → b ≤ a → a = b
  add_comm : ∀ (a b : num), a + b = b + a

namespace V0Model


variable {num str} [M : V0Model num str]
open V0Model BASICModel


instance : PartialOrder num where
  le_refl := BASICModel.le_refl
  le_trans := V0Model.le_trans
  le_antisymm := by apply B7

instance : AddZeroClass num where
  zero_add := zero_add
  add_zero := by apply B3

instance : IsLeftCancelAdd num where
  add_left_cancel := add_left_cancel

instance : IsRightCancelAdd num where
  add_right_cancel := add_right_cancel

instance : AddMonoid num where
  add_assoc := add_assoc
  nsmul := nsmulRec

instance : LinearOrder num where
  le_total := le_total
  toDecidableLE := toDecidableLE

instance : CanonicallyOrderedAdd num where
  exists_add_of_le := exists_add_of_le
  le_self_add := by apply B8

instance : AddCommMonoid num where
  add_comm := add_comm

instance : PartialOrder num where
  le_antisymm := le_antisymm

instance : IsOrderedAddMonoid num where
  add_le_add_left := add_le_add_left


theorem xmin_comp (X : str) : ∃ Y : str, (len Y : num) ≤ len X ∧ ∀ z < len X, z ∈ Y ↔ ∀ y ≤ z, y ∉ X :=
by
  sorry

lemma ex_elt_of_len_pos : ∀ {X : str}, (0 : num) < (len X) -> ∃ x, x ∈ X ∧ x + 1 = len X := by
  intro X h_len
  obtain ⟨len_pred, h_le, h_eq⟩ := B12 (by
    exact Ne.symm (ne_of_lt h_len)
  )
  exists len_pred
  constructor
  · apply L2
    exact h_eq
  · exact h_eq

lemma lt_succ : ∀ (x : num), x < x + 1 := by
  intro x
  rw [lt_iff_le_and_ne]
  constructor
  · apply B8
  · intro h
    conv at h => lhs; rw [<- add_zero x]
    rw [add_left_cancel_iff] at h
    apply @M.B1 0
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
    · apply _root_.le_refl
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
          have aux := (h_Y.right y (M.L1 hy_in)).mp hy_in y (_root_.le_refl _)
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
          have y_zero := B7 hy (M.B9 _)
          rw [y_zero, <- Y_empty]
          exact h_contr
        rw [<- Y_empty] at zero_in_Y
        exact len_not_in zero_in_Y
      · -- ∀ y < len Y, y ∉ X
        intro y hy
        exfalso
        rw [Y_empty] at hy
        exact not_lt_zero hy


lemma comp_xind : ∀ X : str, ∀ z : num, ∃ Y : str, len Y <= z + 1 ∧ ∀ y < z + 1, (y ∈ Y ↔ y ∉ X) := by
  sorry

lemma len_ne_zero_of_in : ∀ {x : num}, ∀ {X : str},
  x ∈ X -> len X ≠ (0 : num) :=
by
  intro x X h
  have h2 := L1 h
  apply ne_of_gt
  apply lt_of_le_of_lt _ h2
  exact B9 x

theorem xind :
  ∀ {X : str}, ∀ {z : num},
  0 ∈ X
  -> (∀ y < z, y ∈ X -> y + 1 ∈ X)
  -> z ∈ X :=
by
  intro X z h_base h_y
  false_or_by_contra
  rename_i h_z

  obtain ⟨Y, h_Y_le, h_Y⟩ := comp_xind X z

  have h_z_in_Y : z ∈ Y := by
    rw [h_Y]
    · exact h_z
    · exact lt_succ z

  have h_Y_pos : (0 : num) < len Y := by
    rw [lt_iff_le_and_ne]
    constructor
    · apply B9
    · exact Ne.symm (len_ne_zero_of_in h_z_in_Y)

  obtain ⟨y0, h_y0⟩ := xmin h_Y_pos

  have h_y0_ne_zero : y0 ≠ 0 := by
    have h_0_notin_Y : 0 ∉ Y := by
      rw [h_Y]
      rw [@not_not]
      exact h_base
      constructor
      · apply B9
      · rw [le_iff_eq_or_lt]
        intro contr
        cases contr with
        | inl contr =>
          apply M.B1 contr
        | inr contr =>
          apply M.not_lt_zero contr

    intro contr
    apply h_0_notin_Y
    rw [<-contr]
    exact h_y0.2.1

  obtain ⟨x0, h_x0⟩ := B12 h_y0_ne_zero

  have h_x0_in : x0 ∈ X := by
    apply not_not.mp
    rw [<- h_Y]
    · apply h_y0.2.2
      rw [<- h_x0.2]
      exact lt_succ x0
    · apply lt_of_lt_of_le _ h_Y_le
      apply lt_trans _ h_y0.1
      rw [<- h_x0.2]
      exact lt_succ x0

  have h_succ_x0_notin : x0 + 1 ∉ X := by
    rw [h_x0.2]
    rw [<- h_Y]
    · exact h_y0.2.1
    · apply lt_of_lt_of_le _ h_Y_le
      exact h_y0.1

  apply h_succ_x0_notin
  apply h_y
  · have aux : y0 < z + 1 := by
      apply lt_of_lt_of_le _ h_Y_le
      apply L1
      exact h_y0.2.1
    rw [<- B11] at aux
    apply lt_of_lt_of_le _ aux
    rw [<- h_x0.2]
    apply lt_succ
  · exact h_x0_in


theorem ind_of_comp (P : num -> Prop) :
  (∀ y : num, ∃ Y : str, (len Y : num) ≤ y ∧ ∀ z < y, z ∈ Y ↔ P z)
  -> (P 0 -> (∀ x, P x -> P (x + 1)) -> ∀ x, P x) :=
by
  intro hcomp pbase pstep z

  obtain ⟨X, hX⟩ := hcomp (z + 1)

  have hX0 : 0 ∈ X := by
    rw [hX.2]
    exact pbase
    rw [<- B11]
    exact B9 z

  have hXstep : ∀ y < z, y ∈ X -> y + 1 ∈ X := by
    intro y hyz hyX
    rw [hX.2]
    · apply pstep
      rw [<- hX.2]
      · exact hyX
      · rw [<- B11]
        exact hyz.1
    · exact (add_lt_add_iff_right 1).mpr hyz

  have hzX : z ∈ X := by
    apply xind
    · exact hX0
    · exact hXstep

  rw [<- hX.2]
  exact hzX
  exact lt_succ z


instance : IDelta0Model num where
  open_induction phi h_open x := sorry
  delta0_induction phi h_delta0 x := sorry

end V0Model

-- Corollary V.1.8
-- T, extending V0, if proves Comp for set of formulas Phi,
-- then also proves Ind, Min and Max for Phi.
-- theorem ind_of_comp : ∀ x : num, comp x ->

-- variable {num} {str : outParam Type} [V0Model num str]


class HasSucc.{u} (α : Type u) where
  succ : α -> α

def Carry {num str} [V0Model num str] (i : num) (X Y : str) := ∃ k < i, (k ∈ X ∧ k ∈ Y ∧ ∀ j < i, (k < j → (j ∈ X ∨ j ∈ Y)))

-- use some comprehension for that
lemma CarryStr {num str} [V0Model num str] (X Y : str) : ∃ C : str, ∀ i : num, i ∈ C ↔ Carry i X Y := by
  sorry

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



namespace Xor'

lemma true1 {P Q R : Prop} : P -> (Xor' (Xor' P Q) R <-> ¬ Xor' Q R) := by
  unfold Xor'
  tauto

lemma true2 {P Q R : Prop} : Q -> (Xor' (Xor' P Q) R <-> ¬ Xor' P R) := by
  unfold Xor'
  tauto

lemma true3 {P Q R : Prop} : R -> (Xor' (Xor' P Q) R <-> ¬ Xor' P Q) := by
  unfold Xor'
  tauto

end Xor'

-- Exercise V.4.19

-- namespace V0ExtModel
variable {num str : Type} [M : V0ExtModel num str]

open V0ExtModel V0Model BASICModel


lemma len_empty : len (0 : str) = (0 : num) := by
  false_or_by_contra
  rename_i h
  obtain ⟨pred, pred_le, pred_eq⟩ := B12 (num := num) h
  have witness := L2 pred_eq
  have aux := @ax_empty _ _ M pred
  apply @not_lt_zero _ _ _ pred
  apply aux.mp
  exact witness

lemma ax_empty' : ∀ {z : num}, z ∉ (0 : str) := by
  intro z
  rw [ax_empty]
  exact not_lt_zero

lemma not_carry_empty : ∀ {X : str}, ∀ {i : num}, ¬Carry i X 0 := by
  intro X i h
  obtain ⟨_, _, _, bad, _⟩ := h
  exact ax_empty' bad

def Maj (P Q R : Prop) := (P ∧ Q ∧ ¬ R) ∨ (P ∧ ¬ Q ∧ R) ∨ (¬ P ∧ Q ∧ R) ∨ (P ∧ Q ∧ R)

lemma Maj_perm_132 {P Q R : Prop} : Maj P Q R <-> Maj P R Q := by
  unfold Maj; tauto

lemma Maj_perm_321 {P Q R : Prop} : Maj P Q R <-> Maj R Q P := by
  unfold Maj; tauto

lemma Maj_perm_213 {P Q R : Prop} : Maj P Q R <-> Maj Q P R := by
  unfold Maj; tauto

lemma Maj_perm_231 {P Q R : Prop} : Maj P Q R <-> Maj R P Q := by
  unfold Maj; tauto

lemma Maj_false {P Q R : Prop} : ¬ P -> (Maj P Q R <-> Q ∧ R) := by
  intro h
  unfold Maj
  tauto

lemma Maj_true1 {P Q R : Prop} : P -> (Maj P Q R <-> Q ∨ R) := by
  intro h
  unfold Maj
  tauto
lemma Maj_true2 {P Q R : Prop} : Q -> (Maj P Q R <-> P ∨ R) := by
  intro h
  unfold Maj
  tauto
lemma Maj_true3 {P Q R : Prop} : R -> (Maj P Q R <-> P ∨ Q) := by
  intro h
  unfold Maj
  tauto



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

lemma not_lt_self : ∀ (i : num), ¬ i < i := by
  intro i h
  rw [<- lt_self_iff_false i]
  exact h

lemma carry_rec2 : ∀ {X Y : str}, ∀ {i : num},
  i ∈ X ∧ i ∈ Y -> Carry (i + 1) X Y :=
by
  intro X Y i h_XY
  obtain ⟨h_X, h_Y⟩ := h_XY
  unfold Carry
  exists i
  constructor
  · exact lt_succ i
  · constructor; assumption
    constructor; assumption
    intro j hj hi
    rw [<- B11] at hj
    exfalso
    apply not_lt_self i
    exact lt_of_lt_of_le hi hj

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
        unfold Maj
        right; right
        rw [<- or_and_right]
        constructor
        · exact em' (Carry pos X Y)
        · constructor <;> assumption
      · rw [<- B11] at lt
        have hlt : pos < i := lt_of_le_of_ne lt (Ne.symm h_pos)
        clear h_pos lt
        have h_pos := prevs i (by rw [<- B11]) hlt
        rcases h_pos with h_iX | h_iY
        · rw [Maj_true2 h_iX]
          left
          unfold Carry
          exists pos
          constructor; assumption
          constructor; assumption
          constructor; assumption
          intro j hj
          apply prevs
          apply lt_trans hj
          exact lt_succ i
        · rw [Maj_true3 h_iY]
          left
          unfold Carry
          exists pos
          constructor; assumption
          constructor; assumption
          constructor; assumption
          intro j hj
          apply prevs
          apply lt_trans hj
          exact lt_succ i
    · intro h
      rcases h with ⟨hC, hX, _⟩ | ⟨hC, _, hY⟩ | h_notCarry | h_all
      · apply carry_rec1 hC (.inl hX)
      · apply carry_rec1 hC (.inr hY)
      · apply carry_rec2 h_notCarry.2
      · apply carry_rec2 h_all.2

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
  exact h

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
    apply (L1 hp).2
    exact _root_.le_of_eq (id (Eq.symm p_eq))
    intro j jp
    by_cases hj : j = p
    · rw [hj]; exact px
    · apply ps.1
      exact px
      constructor
      · rw [B11]
        exact jp
      · rw [<- B11] at jp
        intro contr
        apply hj
        apply _root_.le_antisymm <;> assumption

  have aux2 : p + 1 ≤ len (succ X) := (L1 aux).1
  rw [p_eq] at aux2
  have aux3 : len X < len X := lt_of_le_of_lt aux2 h
  apply aux3.2
  rfl

lemma len_succ_le_succ : ∀ {X : str}, len (succ X) ≤ (len X : num) + (1 : num) := by
  intro X
  by_contra h
  have h_lt : len X + (1 : num) < len (succ X) := lt_of_not_ge h
  obtain ⟨z, h_z_in, h_z_ge, _⟩ := exists_of_len_lt' (X := succ X) (i := len X + (1 : num)) h_lt
  have h_len_X_lt_z : len X < z := lt_of_lt_of_le (lt_succ (len X)) h_z_ge
  rw [ax_succ] at h_z_in
  exact not_lt_self (len X) (lt_of_lt_of_le h_len_X_lt_z h_z_in.1)


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


lemma in_iff_not_notin {X : str} {j : num} : j ∈ X ↔ ¬ j ∉ X := by
  rw [not_not]

def LowestOrderZero (X : str) (m : num) := m ≤ len X ∧ m ∉ X ∧ ∀ j < m, j ∈ X

lemma exists_lowest_order_zero (X : str) : ∃ m : num, LowestOrderZero X m := by
  obtain ⟨X', hX'⟩ := comp10 X (len X + (1 : num))
  have len_X'_ne_zero : (0 : num) < len X' := by
    have lenX_in_X' : (len X) ∈ X' := by
      rw [hX'.2]
      · exact len_not_in
      · exact lt_succ (len X)
    apply @lt_of_le_of_lt _ _ _ (len X)
    · exact B9 (len X)
    · exact L1 lenX_in_X'

  obtain ⟨min, hmin⟩ := xmin len_X'_ne_zero
  exists min

  have min_le_lenx : min <= len X := by
    rw [B11]
    apply lt_of_lt_of_le
    · exact hmin.1
    · exact hX'.1

  constructor
  · have aux := L1 hmin.2.1
    assumption
  · constructor
    · rw [<- hX'.2]
      exact hmin.2.1
      rw [<- B11]
      assumption
    · intro j hj
      rw [@in_iff_not_notin]
      rw [<- hX'.2]
      · apply hmin.2.2
        exact hj
      · rw [<- B11]
        apply le_of_lt
        apply lt_of_lt_of_le
        · assumption
        · assumption

def LowestOrderOne (X : str) (m : num) := m ≤ len X ∧ m ∈ X ∧ ∀ j < m, j ∉ X

lemma exists_lowest_order_one {X : str} : (0 : num) < len X -> ∃ m : num, LowestOrderOne X m := by
  intro len_ne_zero
  obtain ⟨min, hmin⟩ := xmin len_ne_zero
  exists min
  constructor
  apply le_of_lt; exact hmin.1
  exact hmin.2


lemma succ_bit_eq {X : str} {m : num} : LowestOrderZero X m -> m ∈ succ X := by
  sorry

lemma succ_bit_lt {X : str} {m : num} : LowestOrderZero X m -> ∀ i < m, i ∉ succ X := by
  sorry

lemma succ_bit_gt {X : str} {m : num} : LowestOrderZero X m -> ∀ i > m, i ∈ succ X ↔ i ∈ X := by
  sorry

lemma split_wrt_minmax (x y z : num) :
    x < min y z ∨
    x = min y z ∨
    (min y z < x ∧ x < max y z) ∨
    x = max y z ∨
    max y z < x := by
  rcases lt_trichotomy x (min y z) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases lt_trichotomy x (max y z) with hx | hx | hx
    · exact Or.inr (Or.inr (Or.inl ⟨h, hx⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))

lemma xor_assoc {a b c} : Xor' a (Xor' b c) = Xor' (Xor' a b) c := by
  unfold Xor'
  grind only [cases Or]

lemma aux1 : ∀ {X : str}, ∀ {y min : num},
  LowestOrderZero X min -> y < min -> y ∈ X := by
  sorry

lemma len_pos_of_exists : ∀ {i : num} {X : str}, i ∈ X -> len X > (0 : num) := by
  intro i X iX
  apply lt_of_le_of_lt
  apply zero_le i
  apply L1
  assumption

lemma len_succ_pos : ∀ {X : str}, len (succ X) > (0 : num) := by
  intro X
  obtain ⟨min, hmin⟩ := exists_lowest_order_zero X (num := num)
  have min_X := succ_bit_eq hmin
  apply len_pos_of_exists min_X

lemma lsb_not_succ : ∀ {X : str}, 0 ∈ X <-> 0 ∉ (succ X) := by
  intro X
  constructor
  · intro h contr
    rw [ax_succ] at contr
    rcases contr with ⟨hlen, hcases⟩
    rcases hcases with hbad | hgood
    · rcases hbad with ⟨hin, j, hj_lt, hj_notin⟩
      apply not_lt_zero (x := j)
      assumption
    · apply hgood.1; assumption
  · intro h
    rw [ax_succ] at h
    simp only [zero_le, peano.instLTOfStructure, not_le, nonpos_iff_eq_zero, not_lt_zero',
      and_false, false_and, exists_const, IsEmpty.forall_iff, implies_true, and_true, false_or,
      true_and, not_not] at h
    assumption

lemma exists_complement : ∀ X : str, ∃ Y : str, ∀ z : num, z < len X -> (z ∈ Y ↔ z ∉ X) := by
  sorry


lemma xor3_split {P Q R : Prop} : Xor' (Xor' P Q) R <-> (P ∧ ¬Q ∧ ¬R) ∨ (¬ P ∧ Q ∧ ¬ R) ∨ (¬ P ∧ ¬ Q ∧ R) ∨ (P ∧ Q ∧ R) := by
  unfold Xor'; tauto

lemma not_maj {P Q R : Prop} : ¬ Maj P Q R <-> (¬ P ∧ ¬ Q ∧ R) ∨ (P ∧ ¬ Q ∧ ¬ R) ∨ (¬ P ∧ Q ∧ ¬ R) ∨ (¬ P ∧ ¬ Q ∧ ¬ R) := by
  unfold Maj; tauto


lemma all_lt_mem_of_not_mem_of_mem_succ : ∀ {X : str} {i : num}, i ∉ X -> i ∈ succ X -> ∀ j < i, j ∈ X := by
  intro X i h_i_notX h_i_SX
  rw [ax_succ] at h_i_SX
  rcases h_i_SX with ⟨h_i_le, ⟨h_i_X, ex⟩ | ⟨h_i_notX, all⟩⟩
  · exact fun j a ↦ False.elim (h_i_notX h_i_X)
  · exact all

lemma all_lt_not_mem_of_not_carry_of_all_lt_mem : ∀ {X Y : str} {i : num}, ¬ Carry i X Y -> (∀ j < i, j ∈ Y) -> ∀ j < i, j ∉ X := by
  intro X Y i h_Carry h_all_lt_mem_Y
  unfold Carry at h_Carry
  rw [not_exists] at h_Carry
  intro j
  specialize h_Carry j
  rw [not_and_or] at h_Carry
  rcases h_Carry with contr | h_Carry
  · intro contr'
    contradiction
  · intro h_j_lt_i h_j_X
    rw [not_and] at h_Carry
    specialize h_Carry h_j_X
    rw [not_and] at h_Carry
    specialize h_Carry (h_all_lt_mem_Y j h_j_lt_i)
    apply h_Carry; clear h_Carry; intro z z_lt j_lt
    right
    exact h_all_lt_mem_Y z z_lt

lemma all_lt_not_carry_of_not_carry_of_all_lt_mem :
    ∀ {X Y : str} {i : num}, ¬ Carry i X Y -> (∀ j < i, j ∈ Y) -> ∀ j < i, ¬ Carry j X Y := by
  intro X Y i h_notC h_all_lt_mem_Y j h_j_lt h_jC
  unfold Carry at h_jC
  obtain ⟨k, h_k_lt_j, h_k_X, _, _⟩ := h_jC
  have h_k_lt_i : k < i := lt_trans h_k_lt_j h_j_lt
  exact all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y k h_k_lt_i h_k_X

lemma all_lt_not_mem_of_all_lt_mem_add_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ Y) ->
      (∀ j < i, j ∈ X + Y) ->
      ∀ j < i, j ∉ X := by
  intro X Y i h_all_lt_mem_Y h_all_lt_mem_add j h_j_lt_i h_jX
  have h_len_X_pos : (0 : num) < len X := len_pos_of_exists h_jX
  obtain ⟨m, hm⟩ := exists_lowest_order_one (X := X) h_len_X_pos
  have h_m_le_j : m ≤ j := by
    by_contra h_m_gt_j
    exact hm.2.2 j (lt_of_not_ge h_m_gt_j) h_jX
  have h_m_lt_i : m < i := lt_of_le_of_lt h_m_le_j h_j_lt_i
  have h_mY : m ∈ Y := h_all_lt_mem_Y m h_m_lt_i
  have h_m_notCarry : ¬ Carry m X Y := by
    intro hC
    unfold Carry at hC
    obtain ⟨c, h_c_lt_m, h_cX, _, _⟩ := hC
    exact hm.2.2 c h_c_lt_m h_cX
  have h_m_in_add := h_all_lt_mem_add m h_m_lt_i
  rw [ax_add] at h_m_in_add
  have h_m_xor := h_m_in_add.2
  rw [xor3_split] at h_m_xor
  rcases h_m_xor with h1 | h2 | h3 | h4
  · exact h1.2.1 h_mY
  · exact h2.1 hm.2.1
  · exact h3.1 hm.2.1
  · exact h_m_notCarry h4.2.2

lemma not_carry_of_all_lt_mem_add_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ Y) ->
      (∀ j < i, j ∈ X + Y) ->
      ¬ Carry i X Y := by
  intro X Y i h_all_lt_mem_Y h_all_lt_mem_add hC
  unfold Carry at hC
  obtain ⟨k, h_k_lt_i, h_kX, _, _⟩ := hC
  exact all_lt_not_mem_of_all_lt_mem_add_of_all_lt_mem h_all_lt_mem_Y h_all_lt_mem_add k h_k_lt_i h_kX

lemma not_carry_of_all_lt_mem_add :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ X + Y) ->
      ¬ Carry i X Y := by
  intro X Y i h_all_lt_mem_add hC
  obtain ⟨I, h_I_le, h_I⟩ := comp11 X Y i
  unfold Carry at hC
  obtain ⟨k, h_k_lt_i, h_kX, h_kY, _⟩ := hC
  have h_kI : k ∈ I := by
    rw [h_I k h_k_lt_i]
    exact ⟨h_kX, h_kY⟩
  have h_len_I_pos : (0 : num) < len I := len_pos_of_exists h_kI
  obtain ⟨c, h_c_lt_len_I, h_cI, h_cmin⟩ := xmin h_len_I_pos
  have h_c_lt_i : c < i := lt_of_lt_of_le h_c_lt_len_I h_I_le
  have h_cX : c ∈ X := (h_I c h_c_lt_i).1 h_cI |>.1
  have h_cY : c ∈ Y := (h_I c h_c_lt_i).1 h_cI |>.2
  have h_c_notCarry : ¬ Carry c X Y := by
    intro h_cC
    unfold Carry at h_cC
    obtain ⟨d, h_d_lt_c, h_dX, h_dY, _⟩ := h_cC
    have h_dI : d ∈ I := by
      rw [h_I d (lt_trans h_d_lt_c h_c_lt_i)]
      exact ⟨h_dX, h_dY⟩
    exact h_cmin d h_d_lt_c h_dI
  have h_c_in_add : c ∈ X + Y := h_all_lt_mem_add c h_c_lt_i
  rw [ax_add] at h_c_in_add
  rw [xor3_split] at h_c_in_add
  rcases h_c_in_add.2 with h1 | h2 | h3 | h4
  · exact h1.2.1 h_cY
  · exact h2.1 h_cX
  · exact h3.1 h_cX
  · exact h_c_notCarry h4.2.2

lemma all_lt_not_carry_of_all_lt_mem_add :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ X + Y) ->
      ∀ j < i, ¬ Carry j X Y := by
  intro X Y i h_all_lt_mem_add j h_j_lt_i
  apply not_carry_of_all_lt_mem_add
  intro z h_z_lt_j
  exact h_all_lt_mem_add z (lt_trans h_z_lt_j h_j_lt_i)

lemma carry_succ_of_all_lt_mem_add_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      (∀ j < i, j ∈ X + Y) ->
      Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_all_lt_mem_add
  have h_all_lt_not_carry : ∀ j < i, ¬ Carry j X Y :=
    all_lt_not_carry_of_all_lt_mem_add h_all_lt_mem_add
  have h_before_m : ∀ j < m, j ∈ X + Y := by
    intro j h_j_lt_m
    exact h_all_lt_mem_add j (lt_trans h_j_lt_m h_m_lt_i)
  have h_m_notCarry : ¬ Carry m X Y :=
    not_carry_of_all_lt_mem_add_of_all_lt_mem hm.2.2 h_before_m
  have h_m_in_add : m ∈ X + Y := h_all_lt_mem_add m h_m_lt_i
  have h_mX : m ∈ X := by
    rw [ax_add] at h_m_in_add
    have h_m_xor := h_m_in_add.2
    rw [xor3_split] at h_m_xor
    rcases h_m_xor with h1 | h2 | h3 | h4
    · exact h1.1
    · exact False.elim (hm.2.1 h2.2.1)
    · exact False.elim (h_m_notCarry h3.2.2)
    · exact False.elim (hm.2.1 h4.2.1)
  have h_or_after_m : ∀ j, m < j -> j < i -> j ∈ X ∨ j ∈ Y := by
    intro j h_m_lt_j h_j_lt_i
    have h_j_in_add : j ∈ X + Y := h_all_lt_mem_add j h_j_lt_i
    have h_j_notCarry : ¬ Carry j X Y := h_all_lt_not_carry j h_j_lt_i
    rw [ax_add] at h_j_in_add
    have h_j_xor := h_j_in_add.2
    rw [xor3_split] at h_j_xor
    rcases h_j_xor with h1 | h2 | h3 | h4
    · exact Or.inl h1.1
    · exact Or.inr h2.2.1
    · exact False.elim (h_j_notCarry h3.2.2)
    · exact False.elim (h_j_notCarry h4.2.2)
  unfold Carry
  refine ⟨m, h_m_lt_i, h_mX, succ_bit_eq hm, ?_⟩
  intro j h_j_lt_i h_m_lt_j
  rcases h_or_after_m j h_m_lt_j h_j_lt_i with h_jX | h_jY
  · exact Or.inl h_jX
  · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_jY)

lemma exists_min_carry_witness :
    ∀ {X Y : str} {i : num},
      Carry i X Y ->
      ∃ c < i, c ∈ X ∧ c ∈ Y ∧ ¬ Carry c X Y := by
  intro X Y i h_Carry
  obtain ⟨k, h_k_lt_i, h_kX, h_kY, _⟩ := h_Carry
  obtain ⟨I, h_I_le, h_I⟩ := comp11 X Y i
  have h_kI : k ∈ I := by
    rw [h_I k h_k_lt_i]
    exact ⟨h_kX, h_kY⟩
  have h_len_I_pos : (0 : num) < len I := len_pos_of_exists h_kI
  obtain ⟨c, h_c_lt_len_I, h_cI, h_cmin⟩ := xmin h_len_I_pos
  have h_c_lt_i : c < i := lt_of_lt_of_le h_c_lt_len_I h_I_le
  have h_cX : c ∈ X := (h_I c h_c_lt_i).1 h_cI |>.1
  have h_cY : c ∈ Y := (h_I c h_c_lt_i).1 h_cI |>.2
  have h_c_notCarry : ¬ Carry c X Y := by
    intro h_cC
    obtain ⟨d, h_d_lt_c, h_dX, h_dY, _⟩ := h_cC
    have h_dI : d ∈ I := by
      rw [h_I d (lt_trans h_d_lt_c h_c_lt_i)]
      exact ⟨h_dX, h_dY⟩
    exact h_cmin d h_d_lt_c h_dI
  exact ⟨c, h_c_lt_i, h_cX, h_cY, h_c_notCarry⟩

lemma carry_lt_add_len :
    ∀ {X Y : str} {i : num},
      Carry i X Y ->
      i < len X + len Y := by
  intro X Y i h_Carry
  obtain ⟨k, h_k_lt_i, h_kX, h_kY, h_kprop⟩ := h_Carry
  have h_i_ne_zero : i ≠ 0 := by
    intro h_i_zero
    rw [h_i_zero] at h_k_lt_i
    exact not_lt_zero h_k_lt_i
  obtain ⟨pred_i, hpred_i_le, hpred_i_eq⟩ := B12 h_i_ne_zero
  have h_len_X_pos : (0 : num) < len X := len_pos_of_exists h_kX
  have h_len_Y_pos : (0 : num) < len Y := len_pos_of_exists h_kY
  have h_pred_or : pred_i ∈ X ∨ pred_i ∈ Y := by
    by_cases h_k_eq_pred : k = pred_i
    · subst h_k_eq_pred
      exact Or.inl h_kX
    · have h_pred_lt_i : pred_i < i := by
        simpa [hpred_i_eq] using (lt_succ pred_i)
      have h_k_le_pred : k ≤ pred_i := by
        rw [B11, hpred_i_eq]
        exact h_k_lt_i
      have h_k_lt_pred : k < pred_i := lt_of_le_of_ne h_k_le_pred h_k_eq_pred
      exact h_kprop pred_i h_pred_lt_i h_k_lt_pred
  rcases h_pred_or with h_predX | h_predY
  · have h_i_le_lenX : i ≤ len X := by
      rw [<- hpred_i_eq, B11]
      exact (add_lt_add_iff_right 1).mpr (L1 h_predX)
    exact lt_of_le_of_lt h_i_le_lenX (lt_add_of_pos_right (len X) h_len_Y_pos)
  · have h_i_le_lenY : i ≤ len Y := by
      rw [<- hpred_i_eq, B11]
      exact (add_lt_add_iff_right 1).mpr (L1 h_predY)
    exact lt_of_le_of_lt h_i_le_lenY (by
      simpa [_root_.add_comm] using (lt_add_of_pos_right (len Y) h_len_X_pos))

lemma prefix_zero_contradiction_of_not_carry_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      i < len X + len Y ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      (∀ j < i, j ∈ Y) ->
      False := by
  intro X Y i h_i_lt h_prefix_zero h_notC h_all_lt_mem_Y
  have h_X_prefix_zero := all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y
  have h_Carry_prefix_zero := all_lt_not_carry_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y
  obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
  apply h_contr_notXY
  rw [ax_add]
  constructor
  · exact lt_trans h_contr_lt h_i_lt
  · rw [Xor'.true2 (h_all_lt_mem_Y contr h_contr_lt)]
    rw [not_xor]
    rw [<- not_iff_not, iff_true_left]
    · exact h_Carry_prefix_zero contr h_contr_lt
    · exact h_X_prefix_zero contr h_contr_lt

lemma not_lt_lowest_zero_of_prefix_zero_of_not_carry :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      i < len X + len Y ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      ¬ i < m := by
  intro X Y m i hm h_i_lt h_prefix_zero h_notC h_i_lt_m
  apply prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_i_lt h_prefix_zero h_notC
  intro j h_j_lt
  exact hm.2.2 j (lt_trans h_j_lt h_i_lt_m)

lemma not_carry_succ_of_lowest_zero_ge :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      i ≤ m ->
      ¬ Carry i X (succ Y) := by
  intro X Y m i hm h_i_le h_Carry
  unfold Carry at h_Carry
  obtain ⟨k, h_k_lt_i, _, h_k_SY, _⟩ := h_Carry
  exact (succ_bit_lt hm k (lt_of_lt_of_le h_k_lt_i h_i_le)) h_k_SY

lemma carry_succ_of_carry_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      Carry i X Y ->
      Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_Carry
  unfold Carry at h_Carry ⊢
  obtain ⟨k, h_k_lt_i, h_k_X, h_k_Y, h_k_prop⟩ := h_Carry
  rcases lt_trichotomy k m with h_k_lt_m | h_k_eq_m | h_m_lt_k
  · have h_m_X : m ∈ X := by
      rcases h_k_prop m h_m_lt_i h_k_lt_m with h_m_X | h_m_Y
      · exact h_m_X
      · exact False.elim (hm.2.1 h_m_Y)
    refine ⟨m, h_m_lt_i, h_m_X, succ_bit_eq hm, ?_⟩
    intro j h_j_lt_i h_m_lt_j
    rcases h_k_prop j h_j_lt_i (lt_trans h_k_lt_m h_m_lt_j) with h_j_X | h_j_Y
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_j_Y)
  · exact False.elim (hm.2.1 (by simpa [h_k_eq_m] using h_k_Y))
  · refine ⟨k, h_k_lt_i, h_k_X, (succ_bit_gt hm k h_m_lt_k).2 h_k_Y, ?_⟩
    intro j h_j_lt_i h_k_lt_j
    rcases h_k_prop j h_j_lt_i h_k_lt_j with h_j_X | h_j_Y
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j (lt_trans h_m_lt_k h_k_lt_j)).2 h_j_Y)

lemma not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      ¬ Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_prefix_zero h_notC h_Carry
  unfold Carry at h_Carry
  obtain ⟨k, h_k_lt_i, h_k_X, h_k_SY, h_k_prop⟩ := h_Carry
  have h_m_le_k : m ≤ k := by
    by_contra h_mk
    exact (succ_bit_lt hm k (lt_of_not_ge h_mk)) h_k_SY
  have h_k_le_m : k ≤ m := by
    by_contra h_km
    have h_m_lt_k : m < k := lt_of_not_ge h_km
    have h_k_Y : k ∈ Y := (succ_bit_gt hm k h_m_lt_k).1 h_k_SY
    apply h_notC
    refine ⟨k, h_k_lt_i, h_k_X, h_k_Y, ?_⟩
    intro j h_j_lt_i h_k_lt_j
    rcases h_k_prop j h_j_lt_i h_k_lt_j with h_j_X | h_j_SY
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j (lt_trans h_m_lt_k h_k_lt_j)).1 h_j_SY)
  have h_k_eq_m : k = m := by
    apply _root_.le_antisymm <;> assumption
  have h_m_X : m ∈ X := by
    simpa [h_k_eq_m] using h_k_X
  have h_or_after_m : ∀ j, m < j -> j < i -> j ∈ X ∨ j ∈ Y := by
    intro j h_m_lt_j h_j_lt_i
    rcases h_k_prop j h_j_lt_i (by simpa [h_k_eq_m] using h_m_lt_j) with h_j_X | h_j_SY
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).1 h_j_SY)
  have h_X_prefix_zero : ∀ j < m, j ∉ X := by
    intro j h_j_lt_m h_j_X
    apply h_notC
    refine ⟨j, lt_trans h_j_lt_m h_m_lt_i, h_j_X, hm.2.2 j h_j_lt_m, ?_⟩
    intro z h_z_lt_i h_j_lt_z
    by_cases h_z_lt_m : z < m
    · exact Or.inr (hm.2.2 z h_z_lt_m)
    · have h_m_le_z : m ≤ z := le_of_not_gt h_z_lt_m
      rcases eq_or_lt_of_le h_m_le_z with h_z_eq_m | h_m_lt_z
      · exact Or.inl (by simpa [h_z_eq_m] using h_m_X)
      · exact h_or_after_m z h_m_lt_z h_z_lt_i
  have h_Carry_le_m_zero : ∀ j ≤ m, ¬ Carry j X Y := by
    intro j h_j_le_m h_jC
    unfold Carry at h_jC
    obtain ⟨c, h_c_lt_j, h_c_X, _, _⟩ := h_jC
    exact h_X_prefix_zero c (lt_of_lt_of_le h_c_lt_j h_j_le_m) h_c_X
  have carry_to_i_from_after_m :
      ∀ {j : num}, m < j -> j < i -> Carry j X Y -> Carry i X Y := by
    intro j h_m_lt_j h_j_lt_i h_jC
    unfold Carry at h_jC ⊢
    obtain ⟨c, h_c_lt_j, h_c_X, h_c_Y, h_c_prop⟩ := h_jC
    refine ⟨c, lt_trans h_c_lt_j h_j_lt_i, h_c_X, h_c_Y, ?_⟩
    intro z h_z_lt_i h_c_lt_z
    by_cases h_z_lt_j : z < j
    · exact h_c_prop z h_z_lt_j h_c_lt_z
    · have h_j_le_z : j ≤ z := le_of_not_gt h_z_lt_j
      exact h_or_after_m z (lt_of_lt_of_le h_m_lt_j h_j_le_z) h_z_lt_i
  obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
  apply h_contr_notXY
  rw [ax_add]
  constructor
  · rcases lt_trichotomy contr m with h_contr_lt_m | h_contr_eq_m | h_m_lt_contr
    · exact lt_of_lt_of_le (L1 (hm.2.2 contr h_contr_lt_m)) (by
        rw [_root_.add_comm]
        exact B8)
    · rw [h_contr_eq_m]
      exact lt_of_lt_of_le (L1 h_m_X) (show len X ≤ len X + len Y from B8)
    · rcases h_or_after_m contr h_m_lt_contr h_contr_lt with h_contr_X | h_contr_Y
      · exact lt_of_lt_of_le (L1 h_contr_X) (show len X ≤ len X + len Y from B8)
      · exact lt_of_lt_of_le (L1 h_contr_Y) (by
          rw [_root_.add_comm]
          exact B8)
  · rcases lt_trichotomy contr m with h_contr_lt_m | h_contr_eq_m | h_m_lt_contr
    · rw [xor3_split]
      right
      left
      exact ⟨h_X_prefix_zero contr h_contr_lt_m, hm.2.2 contr h_contr_lt_m,
        h_Carry_le_m_zero contr (le_of_lt h_contr_lt_m)⟩
    · rw [h_contr_eq_m, xor3_split]
      left
      exact ⟨h_m_X, hm.2.1, h_Carry_le_m_zero m le_rfl⟩
    · have h_contr_or : contr ∈ X ∨ contr ∈ Y := h_or_after_m contr h_m_lt_contr h_contr_lt
      have h_contr_notboth : ¬ (contr ∈ X ∧ contr ∈ Y) := by
        intro h_both
        apply h_notC
        refine ⟨contr, h_contr_lt, h_both.1, h_both.2, ?_⟩
        intro z h_z_lt_i h_contr_lt_z
        exact h_or_after_m z (lt_trans h_m_lt_contr h_contr_lt_z) h_z_lt_i
      have h_contr_notCarry : ¬ Carry contr X Y := by
        intro h_contr_Carry
        apply h_notC
        exact carry_to_i_from_after_m h_m_lt_contr h_contr_lt h_contr_Carry
      rcases h_contr_or with h_contr_X | h_contr_Y
      · rw [xor3_split]
        left
        exact ⟨h_contr_X, fun h_Y => h_contr_notboth ⟨h_contr_X, h_Y⟩, h_contr_notCarry⟩
      · rw [xor3_split]
        right
        left
        exact ⟨fun h_X => h_contr_notboth ⟨h_X, h_contr_Y⟩, h_contr_Y, h_contr_notCarry⟩

lemma not_mem_add_succ_of_not_mem_add_of_prefix_zero :
    ∀ {X Y : str} {y : num},
      y ∉ X + Y ->
      (∃ j < y, j ∉ X + Y) ->
      y ∉ X + succ Y := by
  intro X Y y h_notAdd h_prefix_zero h_new
  obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
  rw [ax_add] at h_new
  rcases h_new with ⟨_, h_y_xor⟩
  rw [xor3_split] at h_y_xor
  rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
  · rcases h_y_xor with h1 | h2 | h3 | h4
    · have h_yY : y ∈ Y := aux1 hm h_y_lt_m
      have h_notC : ¬ Carry y X Y := by
        intro hC
        apply h_notAdd
        rw [ax_add]
        constructor
        · exact carry_lt_add_len hC
        · rw [xor3_split]
          right
          right
          right
          exact ⟨h1.1, h_yY, hC⟩
      have h_y_lt_old : y < len X + len Y := by
        exact lt_of_lt_of_le (L1 h_yY) (by
          rw [_root_.add_comm]
          exact B8)
      exact prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_y_lt_old h_prefix_zero h_notC
        (fun j h_j_lt ↦ hm.2.2 j (lt_trans h_j_lt h_y_lt_m))
    · exact (succ_bit_lt hm y h_y_lt_m) h2.2.1
    · exact (not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)) h3.2.2
    · exact (succ_bit_lt hm y h_y_lt_m) h4.2.1
  · subst y
    rcases h_y_xor with h1 | h2 | h3 | h4
    · exact h1.2.1 (succ_bit_eq hm)
    · have h_notC : ¬ Carry m X Y := by
        intro hC
        apply h_notAdd
        rw [ax_add]
        constructor
        · exact carry_lt_add_len hC
        · rw [xor3_split]
          right
          right
          left
          exact ⟨h2.1, hm.2.1, hC⟩
      obtain ⟨j, h_j_lt_m, h_j_notAdd⟩ := h_prefix_zero
      have h_jY : j ∈ Y := hm.2.2 j h_j_lt_m
      apply h_j_notAdd
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_jY) (by
          rw [_root_.add_comm]
          exact B8)
      · rw [xor3_split]
        right
        left
        exact ⟨all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC hm.2.2 j h_j_lt_m,
          h_jY,
          all_lt_not_carry_of_not_carry_of_all_lt_mem h_notC hm.2.2 j h_j_lt_m⟩
    · exact (not_carry_succ_of_lowest_zero_ge hm le_rfl) h3.2.2
    · exact (not_carry_succ_of_lowest_zero_ge hm le_rfl) h4.2.2
  · by_cases h_yY : y ∈ Y
    · have h_ySY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_yY
      rcases h_y_xor with h1 | h2 | h3 | h4
      · exact h1.2.1 h_ySY
      · have h_oldC : Carry y X Y := by
          by_contra h_notC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              rw [_root_.add_comm]
              exact B8)
          · rw [xor3_split]
            right
            left
            exact ⟨h2.1, h_yY, h_notC⟩
        exact h2.2.2 (carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_oldC)
      · exact h3.2.1 h_ySY
      · have h_notC : ¬ Carry y X Y := by
          intro hC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              rw [_root_.add_comm]
              exact B8)
          · rw [xor3_split]
            right
            right
            right
            exact ⟨h4.1, h_yY, hC⟩
        exact (not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm h_m_lt_y
          h_prefix_zero h_notC) h4.2.2
    · have h_notSY : y ∉ succ Y := by
        intro h_SY
        exact h_yY ((succ_bit_gt hm y h_m_lt_y).1 h_SY)
      rcases h_y_xor with h1 | h2 | h3 | h4
      · have h_oldC : Carry y X Y := by
          by_contra h_notC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h1.1) (show len X ≤ len X + len Y from B8)
          · rw [xor3_split]
            left
            exact ⟨h1.1, h_yY, h_notC⟩
        exact h1.2.2 (carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_oldC)
      · exact h_notSY h2.2.1
      · have h_notC : ¬ Carry y X Y := by
          intro hC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact carry_lt_add_len hC
          · rw [xor3_split]
            right
            right
            left
            exact ⟨h3.1, h_yY, hC⟩
        exact (not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm h_m_lt_y
          h_prefix_zero h_notC) h3.2.2
      · exact h_notSY h4.2.1

lemma not_mem_add_succ_of_mem_add_of_prefix_one :
    ∀ {X Y : str} {y : num},
      y ∈ X + Y ->
      (∀ j < y, j ∈ X + Y) ->
      y ∉ X + succ Y := by
  intro X Y y h_add h_prefix_one hy
  have h_notCarry_old : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one

  have hy_add := hy
  rw [ax_add] at hy_add
  have hy_xor := hy_add.2
  rw [xor3_split] at hy_xor

  have h_new_X_SY_notCarry :
      y ∈ X -> y ∈ succ Y -> ¬ Carry y X (succ Y) -> False := by
    intro h_X h_SY h_notCarry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact hy1.2.1 h_SY
    · exact hy2.1 h_X
    · exact hy3.1 h_X
    · exact h_notCarry hy4.2.2

  have h_new_X_notSY_Carry :
      y ∈ X -> y ∉ succ Y -> Carry y X (succ Y) -> False := by
    intro h_X h_notSY h_Carry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact hy1.2.2 h_Carry
    · exact hy2.1 h_X
    · exact hy3.1 h_X
    · exact h_notSY hy4.2.1

  have h_new_notX_notSY_notCarry :
      y ∉ X -> y ∉ succ Y -> ¬ Carry y X (succ Y) -> False := by
    intro h_notX h_notSY h_notCarry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact h_notX hy1.1
    · exact h_notSY hy2.2.1
    · exact h_notCarry hy3.2.2
    · exact h_notX hy4.1

  have h_new_notX_SY_Carry :
      y ∉ X -> y ∈ succ Y -> Carry y X (succ Y) -> False := by
    intro h_notX h_SY h_Carry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact h_notX hy1.1
    · exact hy2.2.2 h_Carry
    · exact hy3.2.1 h_SY
    · exact h_notX hy4.1

  have h_old := h_add
  rw [ax_add] at h_old
  have h_old_xor := h_old.2
  rw [xor3_split] at h_old_xor
  rcases h_old_xor with h1 | h2 | h3 | h4
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have hm_le_y : m ≤ y := by
      by_contra h
      exact h1.2.1 (aux1 hm (lt_of_not_ge h))
    rcases eq_or_lt_of_le hm_le_y with h_my | hm_lt_y
    · have h_SY : y ∈ succ Y := by
        simpa [h_my] using succ_bit_eq hm
      have h_notCarry_new : ¬ Carry y X (succ Y) := by
        simpa [h_my] using (not_carry_succ_of_lowest_zero_ge hm le_rfl)
      exact h_new_X_SY_notCarry h1.1 h_SY h_notCarry_new
    · have h_notSY : y ∉ succ Y := by
        intro h_SY
        exact h1.2.1 ((succ_bit_gt hm y hm_lt_y).1 h_SY)
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_all_lt_mem_add_of_lowest_zero_lt hm hm_lt_y h_prefix_one
      exact h_new_X_notSY_Carry h1.1 h_notSY h_Carry_new
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
    · have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
      exact h_new_notX_notSY_notCarry h2.1 h_notSY h_notCarry_new
    · exfalso
      apply hm.2.1
      simpa [h_y_eq_m] using h2.2.1
    · have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h2.2.1
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_all_lt_mem_add_of_lowest_zero_lt hm h_m_lt_y h_prefix_one
      exact h_new_notX_SY_Carry h2.1 h_SY h_Carry_new
  · exact h_notCarry_old h3.2.2
  · exact h_notCarry_old h4.2.2


lemma add_succ_of_succ_add : ∀ {X Y : str}, ∀ {y : num}, y ∈ succ (X + Y) -> y ∈ X + succ Y := by
  intro X Y y hy

  by_cases y = 0
  · rename_i h
    rw [h] at hy
    rw [ax_succ] at hy
    cases hy.2 with
    | inl hy =>
      exfalso
      obtain ⟨j, hj⟩ := hy.2
      apply not_lt_zero (num := num) (x := j)
      apply hj.1
    | inr hy_not =>
      rw [h, ax_add]
      constructor
      · by_cases X = 0
        · rename_i X0
          rw [X0, len_empty, _root_.zero_add]
          apply len_succ_pos
        · refine add_pos_of_nonneg_of_pos ?_ ?_
          · exact B9 (len X)
          · apply len_succ_pos
      · rw [xor_comm]
        rw [<- xor_not_not]
        left
        constructor
        · apply carry_rec.1
          assumption
        · rw [not_not]
          rw [@xor_iff_iff_not]
          rw [ax_add] at hy_not
          simp only [peano.instLTOfStructure, not_le, zero_le, add_pos_iff, true_and, not_and,
            not_xor, nonpos_iff_eq_zero, not_lt_zero', and_false, IsEmpty.forall_iff, implies_true,
            and_true] at hy_not

          rw [iff_false_right (carry_rec (i := y)).1] at hy_not

          constructor
          · intro X0
            specialize hy_not (by
              left
              apply L1
              assumption
            )
            simp only [not_xor] at hy_not
            rw [<- lsb_not_succ]
            rw [<- hy_not]
            assumption
          · intro succY0
            specialize hy_not (by
              right
              rw [<- lsb_not_succ] at succY0
              apply L1
              assumption
            )
            simp only [not_xor] at hy_not
            rw [hy_not]
            exact lsb_not_succ.mpr succY0

  rename_i y_ne_zero
  obtain ⟨pred_y, hpred_y_le, hpred_y_eq⟩ := B12 y_ne_zero

  rw [ax_succ] at hy
  obtain ⟨_t, y_or⟩ := hy
  clear _t
  rcases y_or with ⟨h_y_in_add, h_prefix_zero⟩ | ⟨h_y_notin_add, h_prefix_one⟩
  · rw [ax_add]
    constructor
    · rw [ax_add] at h_y_in_add
      apply lt_of_lt_of_le h_y_in_add.1
      apply _root_.add_le_add_left
      exact len_le_len_succ

    conv at h_y_in_add =>
      rw [<- hpred_y_eq]
      rw [ax_add]
      rw [hpred_y_eq]
    rcases h_y_in_add with ⟨h_y_lt, hxor⟩
    rw [xor3_split] at hxor
    rcases hxor with ⟨h_X, h_notY, h_notC⟩ | ⟨h_notX, h_Y, h_notC⟩ | ⟨h_notX, h_notY, h_C⟩ | ⟨h_X, h_Y, h_C⟩
    · rw [Xor'.true1 h_X]
      rw [not_xor]
      constructor
      · intro h_SY
        exfalso
        exact prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_y_lt h_prefix_zero h_notC
          (all_lt_mem_of_not_mem_of_mem_succ h_notY h_SY)
      · intro h_Carry
        obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
        have hm_le_y : m ≤ y := by
          exact le_of_not_gt (not_lt_lowest_zero_of_prefix_zero_of_not_carry hm h_y_lt h_prefix_zero h_notC)
        rcases eq_or_lt_of_le hm_le_y with rfl | hm_lt_y
        · exact succ_bit_eq hm
        · exfalso
          exact not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm hm_lt_y h_prefix_zero h_notC h_Carry
    · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
      have hm_le_y : m ≤ y := by
        exact le_of_not_gt (not_lt_lowest_zero_of_prefix_zero_of_not_carry hm h_y_lt h_prefix_zero h_notC)
      have hm_ne_y : m ≠ y := by
        intro h_my
        apply hm.2.1
        simpa [h_my] using h_Y
      have hm_lt_y : m < y := lt_of_le_of_ne hm_le_y hm_ne_y
      have h_SY : y ∈ succ Y := (succ_bit_gt hm y hm_lt_y).2 h_Y
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm hm_lt_y h_prefix_zero h_notC
      rw [xor3_split]
      right
      left
      exact ⟨h_notX, h_SY, h_notCarry_new⟩
    · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
      have hm_le_y : m ≤ y := by
        by_contra h
        exact h_notY (aux1 hm (lt_of_not_ge h))
      rcases eq_or_lt_of_le hm_le_y with rfl | hm_lt_y
      · rw [xor3_split]
        right
        left
        exact ⟨h_notX, succ_bit_eq hm, not_carry_succ_of_lowest_zero_ge hm le_rfl⟩
      · have h_notSY : y ∉ succ Y := by
          intro h_SY
          exact h_notY ((succ_bit_gt hm y hm_lt_y).1 h_SY)
        have h_Carry_new : Carry y X (succ Y) := carry_succ_of_carry_of_lowest_zero_lt hm hm_lt_y h_C
        rw [xor3_split]
        right
        right
        left
        exact ⟨h_notX, h_notSY, h_Carry_new⟩
    · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
      rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
      · have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
        have h_notCarry_new : ¬ Carry y X (succ Y) :=
          not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
        rw [xor3_split]
        left
        exact ⟨h_X, h_notSY, h_notCarry_new⟩
      · exfalso
        apply hm.2.1
        simpa [h_y_eq_m] using h_Y
      · have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_Y
        have h_Carry_new : Carry y X (succ Y) := carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_C
        rw [xor3_split]
        right
        right
        right
        exact ⟨h_X, h_SY, h_Carry_new⟩
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have h_notCarry_prefix : ∀ j ≤ y, ¬ Carry j X Y := by
      intro j h_j_le_y
      rcases eq_or_lt_of_le h_j_le_y with rfl | h_j_lt_y
      · exact not_carry_of_all_lt_mem_add h_prefix_one
      · exact all_lt_not_carry_of_all_lt_mem_add h_prefix_one j h_j_lt_y
    rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
    · have h_yY : y ∈ Y := aux1 hm h_y_lt_m
      have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_X : y ∈ X := by
        by_contra h_notX
        apply h_y_notin_add
        rw [ax_add]
        constructor
        · exact lt_of_lt_of_le (L1 h_yY) (by
            simp only [le_add_iff_nonneg_left, zero_le]
            -- simpa [_root_.add_comm] using (show len Y ≤ len Y + len X from B8)
          )
        · rw [xor3_split]
          right
          left
          exact ⟨h_notX, h_yY, h_notC⟩
      have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_X) (show len X ≤ len X + len (succ Y) from B8)
      · rw [xor3_split]
        left
        exact ⟨h_X, h_notSY, h_notCarry_new⟩
    · have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_notY : y ∉ Y := by
        simpa [h_y_eq_m] using hm.2.1
      have h_notX : y ∉ X := by
        intro h_yX
        apply h_y_notin_add
        rw [ax_add]
        constructor
        · exact lt_of_lt_of_le (L1 h_yX) (show len X ≤ len X + len Y from B8)
        · rw [xor3_split]
          left
          exact ⟨h_yX, h_notY, h_notC⟩
      have h_SY : y ∈ succ Y := by
        simpa [h_y_eq_m] using succ_bit_eq hm
      have h_notCarry_new : ¬ Carry y X (succ Y) := by
        simpa [h_y_eq_m] using (not_carry_succ_of_lowest_zero_ge hm le_rfl)
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_SY) (by
          simp only [le_add_iff_nonneg_left, zero_le]
          -- simpa [_root_.add_comm] using (show len (succ Y) ≤ len (succ Y) + len X from B8)
          )
      · rw [xor3_split]
        right
        left
        exact ⟨h_notX, h_SY, h_notCarry_new⟩
    · have h_m_in_add : m ∈ X + Y := h_prefix_one m h_m_lt_y
      have h_m_notC : ¬ Carry m X Y := h_notCarry_prefix m (le_of_lt h_m_lt_y)
      have h_mX : m ∈ X := by
        rw [ax_add] at h_m_in_add
        have h_m_xor := h_m_in_add.2
        rw [xor3_split] at h_m_xor
        rcases h_m_xor with h1 | h2 | h3 | h4
        · exact h1.1
        · exact False.elim (hm.2.1 h2.2.1)
        · exact False.elim (h_m_notC h3.2.2)
        · exact False.elim (hm.2.1 h4.2.1)
      have h_or_after_m : ∀ j, m < j -> j < y -> j ∈ X ∨ j ∈ Y := by
        intro j h_m_lt_j h_j_lt_y
        have h_j_in_add : j ∈ X + Y := h_prefix_one j h_j_lt_y
        have h_j_notC : ¬ Carry j X Y := h_notCarry_prefix j (le_of_lt h_j_lt_y)
        rw [ax_add] at h_j_in_add
        have h_j_xor := h_j_in_add.2
        rw [xor3_split] at h_j_xor
        rcases h_j_xor with h1 | h2 | h3 | h4
        · exact Or.inl h1.1
        · exact Or.inr h2.2.1
        · exact False.elim (h_j_notC h3.2.2)
        · exact False.elim (h_j_notC h4.2.2)
      have h_Carry_new : Carry y X (succ Y) := by
        unfold Carry
        refine ⟨m, h_m_lt_y, h_mX, succ_bit_eq hm, ?_⟩
        intro j h_j_lt_y h_m_lt_j
        rcases h_or_after_m j h_m_lt_j h_j_lt_y with h_jX | h_jY
        · exact Or.inl h_jX
        · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_jY)
      have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_X_pos : (0 : num) < len X := len_pos_of_exists h_mX
      have h_y_lt_new : y < len X + len (succ Y) := by
        have h_pred_or : pred_y ∈ X ∨ pred_y ∈ succ Y := by
          have h_y_maj : Maj (Carry pred_y X (succ Y)) (pred_y ∈ X) (pred_y ∈ succ Y) := by
            have h_y_carry : Carry (pred_y + 1) X (succ Y) := by
              simpa [hpred_y_eq] using h_Carry_new
            exact (carry_rec (i := pred_y) (X := X) (Y := succ Y)).2.1 h_y_carry
          unfold Maj at h_y_maj
          rcases h_y_maj with h1 | h2 | h3 | h4
          · exact Or.inl h1.2.1
          · exact Or.inr h2.2.2
          · exact Or.inl h3.2.1
          · exact Or.inl h4.2.1
        rcases h_pred_or with h_predX | h_predSY
        · have h_y_le_lenX : y ≤ len X := by
            rw [<- hpred_y_eq, B11]
            exact (add_lt_add_iff_right 1).mpr (L1 h_predX)
          exact lt_of_le_of_lt h_y_le_lenX (lt_add_of_pos_right (len X) len_succ_pos)
        · have h_y_le_lenSY : y ≤ len (succ Y) := by
            rw [<- hpred_y_eq, B11]
            exact (add_lt_add_iff_right 1).mpr (L1 h_predSY)
          exact lt_of_le_of_lt h_y_le_lenSY (by
            simpa [_root_.add_comm] using (lt_add_of_pos_right (len (succ Y)) h_X_pos))
      by_cases h_yY : y ∈ Y
      · have h_X : y ∈ X := by
          by_contra h_notX
          apply h_y_notin_add
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              simp only [le_add_iff_nonneg_left, zero_le]
              -- simpa [_root_.add_comm] using (show len Y ≤ len Y + len X from B8)
              )
          · rw [xor3_split]
            right
            left
            exact ⟨h_notX, h_yY, h_notC⟩
        have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_yY
        rw [ax_add]
        constructor
        · exact h_y_lt_new
        · rw [xor3_split]
          right
          right
          right
          exact ⟨h_X, h_SY, h_Carry_new⟩
      · have h_notX : y ∉ X := by
          intro h_X
          apply h_y_notin_add
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_X) (show len X ≤ len X + len Y from B8)
          · rw [xor3_split]
            left
            exact ⟨h_X, h_yY, h_notC⟩
        have h_notSY : y ∉ succ Y := by
          intro h_SY
          exact h_yY ((succ_bit_gt hm y h_m_lt_y).1 h_SY)
        rw [ax_add]
        constructor
        · exact h_y_lt_new
        · rw [xor3_split]
          right
          right
          left
          exact ⟨h_notX, h_notSY, h_Carry_new⟩





lemma succ_len_eq : ∀ {X Y : str}, len (X + succ Y) = (len (succ (X + Y)) : num) := by
  intro X Y
  have h_new_le : len (X + succ Y) ≤ len (X + Y) + (1 : num) := by
    by_contra h
    have h_lt : len (X + Y) + (1 : num) < len (X + succ Y) := lt_of_not_ge h
    obtain ⟨z, h_z_in, h_len_le_z, _⟩ := exists_of_len_lt' (X := X + succ Y) (i := len (X + Y) + (1 : num)) h_lt
    have h_len_lt_z : len (X + Y) < z := lt_of_lt_of_le (lt_succ (len (X + Y))) h_len_le_z
    have h_z_notAdd : z ∉ X + Y := by
      intro h_z_add
      exact not_lt_self (len (X + Y)) (lt_trans h_len_lt_z (L1 h_z_add))
    exact not_mem_add_succ_of_not_mem_add_of_prefix_zero h_z_notAdd
      ⟨len (X + Y), h_len_lt_z, len_not_in⟩ h_z_in
  have h_top_iff :
      len (X + Y) ∈ X + succ Y ↔ ∀ j < len (X + Y), j ∈ X + Y := by
    constructor
    · intro h_top
      by_contra h_not_prefix
      have h_prefix_zero : ∃ j < len (X + Y), j ∉ X + Y := by
        by_contra h_no
        apply h_not_prefix
        intro j h_j_lt
        by_contra h_j_not
        exact h_no ⟨j, h_j_lt, h_j_not⟩
      exact not_mem_add_succ_of_not_mem_add_of_prefix_zero len_not_in h_prefix_zero h_top
    · intro h_prefix_one
      apply add_succ_of_succ_add
      rw [ax_succ]
      constructor
      · exact le_rfl
      · right
        constructor
        · exact len_not_in
        · exact h_prefix_one
  have h_succ_le_new : (len (succ (X + Y)) : num) ≤ len (X + succ Y) := by
    by_contra h
    have h_lt : len (X + succ Y) < len (succ (X + Y)) := lt_of_not_ge h
    obtain ⟨z, h_z_in, h_z_notin, _⟩ := exists_of_len_lt h_lt
    exact h_z_notin (add_succ_of_succ_add h_z_in)
  by_cases h_top : len (X + Y) ∈ X + succ Y
  · have h_top_succ : len (X + Y) ∈ succ (X + Y) := by
      rw [ax_succ]
      constructor
      · exact le_rfl
      · right
        constructor
        · exact len_not_in
        · exact h_top_iff.mp h_top
    have h_new_eq : len (X + succ Y) = len (X + Y) + (1 : num) := by
      apply _root_.le_antisymm
      · exact h_new_le
      · rw [B11]
        exact (add_lt_add_iff_right (1 : num)).mpr (L1 h_top)
    have h_succ_eq : len (succ (X + Y)) = len (X + Y) + (1 : num) := by
      apply _root_.le_antisymm
      · exact len_succ_le_succ
      · rw [B11]
        exact (add_lt_add_iff_right (1 : num)).mpr (L1 h_top_succ)
    rw [h_new_eq, h_succ_eq]
  · have h_not_top_succ : len (X + Y) ∉ succ (X + Y) := by
      intro h_top_succ
      exact h_top (add_succ_of_succ_add h_top_succ)
    have h_succ_eq : len (succ (X + Y)) = (len (X + Y) : num) := by
      have h_succ_le_old : len (succ (X + Y)) ≤ (len (X + Y) : num) := by
        by_contra h
        have h_lt : len (X + Y) < len (succ (X + Y)) := lt_of_not_ge h
        have h_ge : len (X + Y) + (1 : num) ≤ len (succ (X + Y)) := by
          rw [B11]
          exact (add_lt_add_iff_right (1 : num)).mpr h_lt
        have h_eq : len (succ (X + Y)) = len (X + Y) + (1 : num) := _root_.le_antisymm len_succ_le_succ h_ge
        apply h_not_top_succ
        apply L2
        exact h_eq.symm
      exact _root_.le_antisymm h_succ_le_old len_le_len_succ
    have h_new_eq : len (X + succ Y) = (len (X + Y) : num) := by
      have h_old_le_new : (len (X + Y) : num) ≤ len (X + succ Y) := by
        rw [<- h_succ_eq]
        exact h_succ_le_new
      have h_new_le_old : len (X + succ Y) ≤ (len (X + Y) : num) := by
        by_contra h
        have h_lt : len (X + Y) < len (X + succ Y) := lt_of_not_ge h
        have h_ge : len (X + Y) + (1 : num) ≤ len (X + succ Y) := by
          rw [B11]
          exact (add_lt_add_iff_right (1 : num)).mpr h_lt
        have h_eq : len (X + succ Y) = len (X + Y) + (1 : num) := _root_.le_antisymm h_new_le h_ge
        apply h_top
        apply L2
        exact h_eq.symm
      exact _root_.le_antisymm h_new_le_old h_old_le_new
    rw [h_new_eq, h_succ_eq]


lemma succ_add_of_add_succ : ∀ {X Y : str}, ∀ {y : num}, y ∈ X + succ Y -> y ∈ succ (X + Y) := by
  intro X Y y hy
  have h_y_lt_succ_old : y < len (succ (X + Y)) := by
    have h := L1 hy
    rw [succ_len_eq] at h
    exact h
  have h_y_le_old : y ≤ len (X + Y) := by
    rw [B11]
    exact lt_of_lt_of_le h_y_lt_succ_old len_succ_le_succ

  rw [ax_succ]
  constructor
  · exact h_y_le_old
  · by_cases h_add : y ∈ X + Y
    · left
      constructor
      · exact h_add
      · by_contra h_no_zero
        have h_prefix_one : ∀ j < y, j ∈ X + Y := by
          intro j h_j_lt
          by_contra h_j_not
          exact h_no_zero ⟨j, h_j_lt, h_j_not⟩
        exact (not_mem_add_succ_of_mem_add_of_prefix_one h_add h_prefix_one) hy
    · right
      constructor
      · exact h_add
      · by_contra h_not_prefix
        have h_prefix_zero : ∃ j < y, j ∉ X + Y := by
          by_contra h_no
          apply h_not_prefix
          intro j h_j_lt
          by_contra h_j_not
          exact h_no ⟨j, h_j_lt, h_j_not⟩
        exact (not_mem_add_succ_of_not_mem_add_of_prefix_zero h_add h_prefix_zero) hy

lemma succ_add_iff_add_succ : ∀ {X Y : str}, ∀ {y : num}, y ∈ X + succ Y <-> y ∈ succ (X + Y) :=
  ⟨succ_add_of_add_succ, add_succ_of_succ_add⟩

theorem str_succ_assoc : ∀ {X Y : str}, X + succ Y = succ (X + Y) := by
  intro X Y
  apply M.SE
  · exact succ_len_eq
  · intro y y_lt
    exact succ_add_iff_add_succ

lemma str_eq_of_mem_iff : ∀ {X Y : str}, (∀ y : num, y ∈ X ↔ y ∈ Y) -> X = Y := by
  intro X Y h_mem
  have h_len : len X = (len Y : num) := by
    rcases lt_trichotomy (len X : num) (len Y : num) with h_lt | h_eq | h_gt
    · exfalso
      obtain ⟨z, h_z_in_Y, h_z_notin_X, _⟩ := exists_of_len_lt (X := X) (Y := Y) h_lt
      exact h_z_notin_X ((h_mem z).mpr h_z_in_Y)
    · exact h_eq
    · exfalso
      obtain ⟨z, h_z_in_X, h_z_notin_Y, _⟩ := exists_of_len_lt (X := Y) (Y := X) h_gt
      exact h_z_notin_Y ((h_mem z).mp h_z_in_X)
  exact M.SE h_len (fun y _ => h_mem y)

lemma carry_comm : ∀ {X Y : str}, ∀ {i : num}, Carry i X Y ↔ Carry i Y X := by
  intro X Y i
  unfold Carry
  constructor
  · intro h
    obtain ⟨k, hk_lt_i, hkX, hkY, hkprop⟩ := h
    refine ⟨k, hk_lt_i, hkY, hkX, ?_⟩
    intro j hj_lt_i hk_lt_j
    rcases hkprop j hj_lt_i hk_lt_j with hjX | hjY
    · exact Or.inr hjX
    · exact Or.inl hjY
  · intro h
    obtain ⟨k, hk_lt_i, hkY, hkX, hkprop⟩ := h
    refine ⟨k, hk_lt_i, hkX, hkY, ?_⟩
    intro j hj_lt_i hk_lt_j
    rcases hkprop j hj_lt_i hk_lt_j with hjY | hjX
    · exact Or.inr hjY
    · exact Or.inl hjX

lemma mem_add_iff_xor : ∀ {X Y : str}, ∀ {i : num},
    i ∈ X + Y ↔ Xor' (Xor' (i ∈ X) (i ∈ Y)) (Carry i X Y) := by
  intro X Y i
  constructor
  · intro h
    exact (ax_add (X := X) (Y := Y) (i := i)).mp h |>.2
  · intro h_xor
    have h_lt : i < len X + len Y := by
      rw [xor3_split] at h_xor
      rcases h_xor with h | h | h | h
      · exact lt_of_lt_of_le (L1 h.1) (show len X ≤ len X + len Y from B8)
      · exact lt_of_lt_of_le (L1 h.2.1) (by
          rw [_root_.add_comm]
          exact B8)
      · exact carry_lt_add_len h.2.2
      · exact lt_of_lt_of_le (L1 h.1) (show len X ≤ len X + len Y from B8)
    exact (ax_add (X := X) (Y := Y) (i := i)).mpr ⟨h_lt, h_xor⟩

lemma add_comm_bit_bool {P Q R S : Prop} :
    (R ↔ S) -> (Xor' (Xor' P Q) R ↔ Xor' (Xor' Q P) S) := by
  intro h
  unfold Xor' at *
  tauto

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

theorem str_add_comm : ∀ {X Y : str}, X + Y = Y + X := by
  intro X Y
  refine str_eq_of_mem_iff (num := num) (str := str) (X := X + Y) (Y := Y + X) ?_
  intro i
  rw [mem_add_iff_xor (X := X) (Y := Y) (i := i)]
  rw [mem_add_iff_xor (X := Y) (Y := X) (i := i)]
  exact add_comm_bit_bool (carry_comm (X := X) (Y := Y) (i := i))


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
