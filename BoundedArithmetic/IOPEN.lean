-- for a quick demo, jump straight to `theorem add_assoc`
import Mathlib.Tactic.Core
import Mathlib.Logic.Basic
import Mathlib.Tactic

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.IsEnum
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.Syntax
import BoundedArithmetic.Semantics
import BoundedArithmetic.Complexity
import BoundedArithmetic.Order
import BoundedArithmetic.BasicSingleSorted
import BoundedArithmetic.SimpRules

open FirstOrder Language BoundedFormula

class IOPENModel (num : Type*) extends BASICModel num where
  open_induction {n} {a : Type} [IsEnum a]
    (phi : peano.BoundedFormula ((Vars1 n) ⊕ a) 0) :
    phi.IsOpen -> (mkInductionSentence phi).Realize num

namespace IOPENModel

universe u v
variable {M : Type u} [iopen : IOPENModel M]


-- page 36 of draft (47 of pdf)
-- Example 3.8 The following formulas (and their universal closures) are theorems of IOPEN:
open BASICModel Formula Term

open Lean Elab Tactic

theorem forall_swap_231 {α β γ} {p : α -> β -> γ -> Prop}
  : (∀ x y z, p x y z) <-> (∀ z x y, p x y z) :=
  ⟨fun f z x y  => f x y z, fun f y z x => f x y z⟩

-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z
theorem add_assoc
  : ∀ x y z : M, (x + y) + z = x + (y + z) :=
by
  -- TODO: how to make Lean infer these formulas?
  let phi : peano.Formula (Vars3 .z .x .y) :=
    ((x + y) + z) =' (x + (y + z))
  have ind := iopen.open_induction $ display3 .z phi
  unfold phi at ind
  simp_complexity at ind
  simp_induction at ind

  rw [forall_swap_231]
  apply ind ?base ?step; clear ind
  · intro x y
    rw [B3 (x + y)]
    rw [B3 y]
  · intro z hInd x y
    rw [B4]
    rw [B4]
    rw [B4]
    rw [<- (B2 (x + y + z) (x + (y + z)))]
    rw [hInd]

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
-- proof: induction on x
lemma add_zero_comm
  : ∀ x : M, x + 0 = 0 + x :=
by
  have ind := iopen.open_induction $ display1
    (((x + 0) =' (0 + x)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind

  apply ind ?base ?step; clear ind
  · trivial
  · intro a ha
    rw [← add_assoc]
    rw [← ha]
    rw [B3]
    rw [B3]

-- this is necessary to prove axiom `C` from BasicExt
lemma zero_add
  : ∀ x : M, 0 + x = x :=
by
  intro a
  rw [<- add_zero_comm]
  exact B3 a

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
theorem add_one_comm
  : ∀ x : M, x + 1 = 1 + x :=
by
  have ind := iopen.open_induction $ display1
    (((x + 1) =' (1 + x)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind

  apply ind ?base ?step; clear ind
  · rw [zero_add, B3]
  · intro a ha
    rw [<- add_assoc]
    rw [ha]

#check forall_swap

-- O2. x + y = y + x (Commutativity of +)
-- proof : induction on y, first establishing the special cases y = 0 and y = 1
theorem add_comm
  : ∀ x y : M, x + y = y + x :=
by
  have ind := iopen.open_induction $ display2 .y
    (((x + y) =' (y + x)) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind

  rw [forall_swap]
  apply ind ?base ?step; clear ind
  · intro; rw [add_zero_comm]
  · intro a hInd b
    rw [<- add_assoc]
    rw [hInd]
    rw [add_assoc]
    rw [add_one_comm]
    rw [<- add_assoc]

-- O3. x · (y + z) = (x · y) + (x · z) (Distributive law)
  -- proof: induction on z
theorem mul_add
  : ∀ x y z : M, x * (y + z) = (x * y) + (x * z) :=
by
  have ind := iopen.open_induction $ display3 .z
     ((x * (y + z)) =' ((x * y) + (x * z)) : Formula _ (Vars3 .z .x .y))
  simp_complexity at ind
  simp_induction at ind

  rw [forall_swap_231]
  apply ind ?base ?step; clear ind
  · intro a b
    rw [B3]
    rw [B5]
    rw [B3]
  · intro b hInd_b a2 a3
    rw [add_comm]
    rw [add_assoc]
    rw [add_comm]
    rw [hInd_b]
    conv => lhs; left; rw [add_comm]; rw [B6]
    rw [B6]
    conv => rhs; right; rw [add_comm]
    rw [add_assoc]

theorem mul_one
  : ∀ x : M, x * 1 = x :=
by
  intro x
  rw [<- zero_add 1]
  rw [B6]
  rw [B5]
  rw [add_comm]
  rw [B3]

-- O4. (x · y) · z = x · (y · z) (Associativity of ·)
  -- proof: induction on z, using O3
theorem mul_assoc
  : ∀ x y z : M, (x * y) * z = x * (y * z) :=
by
  have ind := iopen.open_induction $ display3 .z
    ((((x * y) * z) =' (x * (y * z))) : Formula _ (Vars3 .z .x .y))

  simp_complexity at ind
  simp_induction at ind

  rw [forall_swap_231]
  apply ind ?base ?step; clear ind
  · intro x y
    rw [B5]
    rw [B5]
    rw [B5]
  · intro x hInd_x y z
    rw [mul_add]
    rw [mul_add]
    rw [mul_one]
    rw [mul_one]
    rw [mul_add]
    rw [<- hInd_x]

lemma zero_mul
  : ∀ x : M, 0 * x = 0 :=
by
  have ind := iopen.open_induction $ display1
    (((0 * x) =' 0) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step; clear ind
  · rw [B5]
  · intro x hInd_0_x
    rw [B6]
    rw [hInd_0_x]
    rw [B3]

lemma one_mul
  : ∀ x : M, 1 * x = x :=
by
  have ind := iopen.open_induction $ display1
    (((1 * x) =' x) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step; clear ind
  · rw [B5]
  · intro x hInd_1_x
    rw [B6]
    rw [hInd_1_x]

lemma mul_add_1_left
  : ∀ x y : M, (x + 1) * y = x * y + y :=
by
  have ind := iopen.open_induction $ display2 .y
    (((x + 1) * y) =' ((x * y) + y) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_swap]
  apply ind ?base ?step; clear ind
  · intro x
    rw [B5]
    rw [B5]
    rw [B3]
  · intro y hInd_y x
    rw [B6]
    rw [B6]
    rw [hInd_y]
    conv => lhs; rw [add_assoc]; right; rw [<- add_assoc]; left; rw [add_comm]
    conv => rhs; rw [add_assoc]; right; rw [<- add_assoc]

-- O5. x · y = y · x (Commutativity of ·)
theorem mul_comm
  : ∀ x y : M, x * y = y * x :=
by
  have ind := iopen.open_induction $ display2 .y
    (((x * y) =' (y * x)) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_swap]
  apply ind ?base ?step; clear ind
  · intro x
    rw [B5]
    rw [zero_mul]
  · intro x hInd_x y
    rw [B6]
    rw [mul_add_1_left]
    rw [hInd_x]

example : Nonempty (True ∧ True) :=
  ⟨⟨⟨⟩, ⟨⟩⟩⟩

-- O6. x + z = y + z → x = y (Cancellation law for +)
theorem add_cancel_right.mp
  : ∀ {x y z : M}, x + z = y + z → x = y :=
by
  have ind := iopen.open_induction $ display3 .z
    (((x + z) =' (y + z) ⟹ (x =' y)) : Formula _ (Vars3 .z .x .y))

  simp_complexity at ind
  simp_induction at ind

  rw [forall_swap_231]
  apply ind ?base ?step; clear ind
  · intro x y
    rw [B3]
    rw [B3]
    intro h
    exact h
  · intro x hInd_x y z
    conv => lhs; lhs; right; rw [add_comm]
    conv => lhs; rhs; right; rw [add_comm]
    rw [<- add_assoc]
    rw [<- add_assoc]
    intro h
    apply B2
    apply hInd_x
    exact h

theorem add_cancel_right
  : ∀ {x y z : M}, x + z = y + z <-> x = y :=
by
  intro x y z
  constructor
  · exact add_cancel_right.mp
  · intro h
    rw [h]

theorem add_cancel_left
  : ∀ {x y z : M}, z + x = z + y <-> x = y :=
by
  intro x y z
  constructor
  · conv => rw [add_comm]; lhs; rhs; rw [add_comm]
    apply add_cancel_right.mp
  · intro h
    rw [h]

-- O7. 0 ≤ x
theorem zero_le
  : ∀ x : M, 0 ≤ x :=
by
  intro x
  rw [<- B3 x]
  rw [add_comm]
  apply B8

-- O8. x ≤ 0 → x = 0
theorem le_zero_eq
  : ∀ x : M, x ≤ 0 → x = 0 :=
by
  intro x h
  apply B7
  · exact h
  · apply zero_le

-- O9. x ≤ x
-- This is proved already as BASICModel.le_refl (doesn't need induction)
-- theorem le_refl
--   : ∀ x : M, x ≤ x :=
-- by
--   intro x
--   conv => right; rw [<- B3 x]
--   apply B8

-- O10. x ≠ x + 1
theorem ne_succ
  : ∀ x : M, x ≠ x + 1 :=
by
  have ind := iopen.open_induction $ display1
    ((x ≠' (x + 1)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind

  apply ind ?base ?step; clear ind
  · intro h
    -- TODO: why this self is necessary?
    apply B1 (self := iopen.toBASICModel)
    apply Eq.symm
    exact h
  · intro a h hq
    apply h
    apply B2
    exact hq

theorem add_mul
  : ∀ x y z : M, (x + y) * z = x * z + y * z :=
by
  intro x y z
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm]
  conv => lhs; rhs; rw [mul_comm]

end IOPENModel
