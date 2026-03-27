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
  -- obtain ⟨minXY, hminXY⟩ := exists_lowest_order_zero (X + Y) (num := num)
  -- obtain ⟨minY, hminY⟩ := exists_lowest_order_zero Y (num := num)

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
        -- Now, this is impossible for any `j < y` to `j ∉ X + Y`.
        exfalso

        have h_Y_prefix_one := all_lt_mem_of_not_mem_of_mem_succ h_notY h_SY
        have h_X_prefix_zero := all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC h_Y_prefix_one
        have h_Carry_prefix_zero : ∀ j < y, ¬ Carry j X Y := by
          intro j h_j_lt h_Carry
          unfold Carry at h_Carry
          obtain ⟨contr, h_contr_lt, h_contr_X, _, _⟩ := h_Carry
          have h_contr_lt_y : contr < y := lt_trans h_contr_lt h_j_lt
          exact h_X_prefix_zero contr h_contr_lt_y h_contr_X

        obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
        apply h_contr_notXY
        rw [ax_add]
        constructor
        · apply lt_trans h_contr_lt h_y_lt
        · rw [Xor'.true2 (h_Y_prefix_one contr h_contr_lt)]
          rw [not_xor]
          rw [<- not_iff_not, iff_true_left]
          apply h_Carry_prefix_zero contr h_contr_lt
          apply h_X_prefix_zero contr h_contr_lt
      · intro h_Carry
        obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
        have hm_le_y : m ≤ y := by
          by_contra h
          exact h_notY (aux1 hm (lt_of_not_ge h))
        rcases eq_or_lt_of_le hm_le_y with rfl | hm_lt_y
        · exact succ_bit_eq hm
        · exfalso
          unfold Carry at h_Carry
          obtain ⟨k, hk_lt_y, hkX, hkSY, hkprop⟩ := h_Carry
          have hm_le_k : m ≤ k := by
            by_contra h_mk
            exact (succ_bit_lt hm k (lt_of_not_ge h_mk)) hkSY
          have hk_le_m : k ≤ m := by
            by_contra h_km
            have hm_lt_k : m < k := lt_of_not_ge h_km
            have hkY : k ∈ Y := (succ_bit_gt hm k hm_lt_k).1 hkSY
            apply h_notC
            refine ⟨k, hk_lt_y, hkX, hkY, ?_⟩
            intro j hj_lt_y hk_lt_j
            rcases hkprop j hj_lt_y hk_lt_j with hjX | hjSY
            · exact Or.inl hjX
            · exact Or.inr ((succ_bit_gt hm j (lt_trans hm_lt_k hk_lt_j)).1 hjSY)
          have hk_eq_m : k = m := by
            apply _root_.le_antisymm <;> assumption
          have hmX : m ∈ X := by
            simpa [hk_eq_m] using hkX
          have h_or_after_m : ∀ j, m < j -> j < y -> j ∈ X ∨ j ∈ Y := by
            intro j hm_lt_j hj_lt_y
            rcases hkprop j hj_lt_y (by simpa [hk_eq_m] using hm_lt_j) with hjX | hjSY
            · exact Or.inl hjX
            · exact Or.inr ((succ_bit_gt hm j hm_lt_j).1 hjSY)
          have h_X_prefix_zero : ∀ j < m, j ∉ X := by
            intro j hj_lt_m h_jX
            apply h_notC
            refine ⟨j, lt_trans hj_lt_m hm_lt_y, h_jX, hm.2.2 j hj_lt_m, ?_⟩
            intro z hz_lt_y hj_lt_z
            by_cases hz_lt_m : z < m
            · exact Or.inr (hm.2.2 z hz_lt_m)
            · have hm_le_z : m ≤ z := le_of_not_gt hz_lt_m
              rcases eq_or_lt_of_le hm_le_z with hzm | hm_lt_z
              · exact Or.inl (by simpa [hzm] using hmX)
              · exact h_or_after_m z hm_lt_z hz_lt_y
          have h_Carry_le_m_zero : ∀ j ≤ m, ¬ Carry j X Y := by
            intro j hj_le_m h_jC
            unfold Carry at h_jC
            obtain ⟨c, hc_lt_j, hcX, _, _⟩ := h_jC
            exact h_X_prefix_zero c (lt_of_lt_of_le hc_lt_j hj_le_m) hcX
          have carry_to_y_from_after_m :
              ∀ {j : num}, m < j -> j < y -> Carry j X Y -> Carry y X Y := by
            intro j hm_lt_j hj_lt_y h_jC
            unfold Carry at h_jC ⊢
            obtain ⟨c, hc_lt_j, hcX, hcY, hcprop⟩ := h_jC
            refine ⟨c, lt_trans hc_lt_j hj_lt_y, hcX, hcY, ?_⟩
            intro z hz_lt_y hc_lt_z
            by_cases hz_lt_j : z < j
            · exact hcprop z hz_lt_j hc_lt_z
            · have hj_le_z : j ≤ z := le_of_not_gt hz_lt_j
              exact h_or_after_m z (lt_of_lt_of_le hm_lt_j hj_le_z) hz_lt_y
          obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
          apply h_contr_notXY
          rw [ax_add]
          constructor
          · exact lt_trans h_contr_lt h_y_lt
          · rcases lt_trichotomy contr m with h_contr_lt_m | h_contr_eq_m | h_m_lt_contr
            · rw [xor3_split]
              right
              left
              exact ⟨h_X_prefix_zero contr h_contr_lt_m, hm.2.2 contr h_contr_lt_m,
                h_Carry_le_m_zero contr (le_of_lt h_contr_lt_m)⟩
            · rw [h_contr_eq_m, xor3_split]
              left
              exact ⟨hmX, hm.2.1, h_Carry_le_m_zero m le_rfl⟩
            · have h_contr_or : contr ∈ X ∨ contr ∈ Y := h_or_after_m contr h_m_lt_contr h_contr_lt
              have h_contr_notboth : ¬ (contr ∈ X ∧ contr ∈ Y) := by
                intro h_both
                apply h_notC
                refine ⟨contr, h_contr_lt, h_both.1, h_both.2, ?_⟩
                intro z hz_lt_y h_contr_lt_z
                exact h_or_after_m z (lt_trans h_m_lt_contr h_contr_lt_z) hz_lt_y
              have h_contr_notCarry : ¬ Carry contr X Y := by
                intro h_contr_Carry
                apply h_notC
                exact carry_to_y_from_after_m h_m_lt_contr h_contr_lt h_contr_Carry
              rcases h_contr_or with h_contr_X | h_contr_Y
              · rw [xor3_split]
                left
                exact ⟨h_contr_X, fun hY => h_contr_notboth ⟨h_contr_X, hY⟩, h_contr_notCarry⟩
              · rw [xor3_split]
                right
                left
                exact ⟨fun hX => h_contr_notboth ⟨hX, h_contr_Y⟩, h_contr_Y, h_contr_notCarry⟩
    · sorry
    · sorry
    · sorry
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
