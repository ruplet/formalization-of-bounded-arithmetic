-- for a quick demo, jump straight to `theorem add_assoc`
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.IsEnum
import BoundedArithmetic.IsEnumProperties
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.Syntax
import BoundedArithmetic.Complexity
import BoundedArithmetic.Order
import BoundedArithmetic.SimpAttrs
import BoundedArithmetic.BasicSingleSorted

open FirstOrder Language BoundedFormula

class IOPENModel (num : Type*) extends BASICModel num where
  open_induction {disp a : Type} [HasDisplayed disp] [IsEnum a]
    (phi : peano.BoundedFormula (disp ⊕ a) 0) :
    phi.IsOpen -> (mkInductionSentence phi).Realize num

namespace IOPENModel

universe u v
variable (M : Type u) [iopen : IOPENModel M]


-- page 36 of draft (47 of pdf)
-- Example 3.8 The following formulas (and their universal closures) are theorems of IOPEN:
open BASICModel

-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z
theorem add_assoc
  : ∀ x y z : M, (x + y) + z = x + (y + z) :=
by
  -- the below block is a set of repetitive conversion we need to do;
  -- this should be automatized by a single tactic
  have ind := open_induction (self := iopen)
    (display_z_xyz  $ ((x + y) + z) =' (x + (y + z)))
  simp only [delta0_simps] at ind
  specialize ind trivial
  -- now, we cannot simply do `apply ind` without `intros`,
  -- because our induction formula has a different order of quantifiers;
  -- Lean can't unify ∀x y, phi(x, y) with ∀y x, phi(x, y)
  -- see also: refer to Mathlib.Logic.Basic.forall_swap
  intros
  apply ind ?base ?step
  clear ind
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
lemma add_zero_comm
  : ∀ x : M, x + 0 = 0 + x
-- proof: induction on x
:= by
  have ind :=
    open_induction (self := iopen)
      (display_x_x $ ((x + 0) =' (0 + x)))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
  · trivial
  · intro a ha
    rw [← add_assoc]
    rw [← ha]
    rw [B3]
    rw [B3]

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
theorem add_one_comm
  : ∀ x : M, x + 1 = 1 + x :=
by
  have ind := open_induction (self := iopen)
    (display_x_x $ ((x + 1) =' (1 + x)))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
  · rw [C, B3]
  · intro a ha
    rw [<- add_assoc]
    rw [ha]

-- O2. x + y = y + x (Commutativity of +)
-- proof : induction on y, first establishing the special cases y = 0 and y = 1
theorem add_comm
  : ∀ x y : M, x + y = y + x :=
by
  have ind := open_induction (self := iopen) (display_y_xy $ ((x + y) =' (y + x)))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
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
  have ind := open_induction (self := iopen) (display_z_xyz $ ((x * (y + z)) =' ((x * y) + (x * z))))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
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
  rw [<- C]
  rw [B6]
  rw [B5]
  rw [add_comm]
  rw [B3]

-- O4. (x · y) · z = x · (y · z) (Associativity of ·)
  -- proof: induction on z, using O3
theorem mul_assoc
  : ∀ x y z : M, (x * y) * z = x * (y * z) :=
by
  have ind := open_induction (self := iopen)
    (display_z_xyz $ (((x * y) * z) =' (x * (y * z))))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
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
  have ind := open_induction (self := iopen)
    (display_x_x $ (0 * x) =' 0)
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
  · rw [B5]
  · intro x hInd_0_x
    rw [B6]
    rw [hInd_0_x]
    rw [B3]

lemma one_mul
  : ∀ x : M, 1 * x = x :=
by
  have ind := open_induction (self := iopen) (display_x_x $ (1 * x) =' x)
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
  · rw [B5]
  · intro x hInd_1_x
    rw [B6]
    rw [hInd_1_x]

lemma mul_add_1_left
  : ∀ x y : M, (x + 1) * y = x * y + y :=
by
  have ind := open_induction (self := iopen) (display_y_xy $ ((x + 1) * y) =' ((x * y) + y))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
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
  have ind := open_induction (self := iopen) (display_y_xy $ (x * y) =' (y * x))
  simp only [delta0_simps] at ind
  specialize ind trivial
  intros
  apply ind ?base ?step
  clear ind
  · intro x
    rw [B5]
    rw [zero_mul]
  · intro x hInd_x y
    rw [B6]
    rw [mul_add_1_left]
    rw [hInd_x]

-- O6. x + z = y + z → x = y (Cancellation law for +)
theorem add_cancel_right
  : ∀ x y z : M, x + z = y + z → x = y :=
by
  have ind := open_induction (self := iopen) (display_z_xyz $ ((x + z) =' (y + z) ⟹ (x =' y)))
  simp only [delta0_simps] at ind
  specialize ind (by exact ⟨trivial, trivial⟩)
  intros x y z
  apply ind ?base ?step
  clear ind
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
  constructor
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
  have ind := open_induction (self := iopen) (display_x_x $ x ≠' (x + 1))
  simp only [Term.neq, BoundedFormula.not, delta0_simps] at ind
  specialize ind (by
    refine ⟨trivial, isQF_bot⟩
  )
  intro x
  apply ind ?base ?step
  clear ind
  · intro h
    -- TODO: why this self is necessary?
    apply B1 (self := iopen.toBASICModel)
    apply Eq.symm
    exact h
  · intro a h hq
    apply h
    apply B2
    exact hq

-- lemma a (x : Nat) : x + 1 ≠ 0 := by
--   apply?

-- #check B1

theorem isAddRightRegular_one : IsAddRightRegular (1 : M) := by
  unfold IsAddRightRegular Function.Injective
  exact B2

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
  zero_add := by
    intro a
    rw [<- add_zero_comm]
    exact B3 a
  add_zero := by
    exact B3
  nsmul := nsmulRec
  add_comm := add_comm M

-- instance : IsRightCancelAdd M where
--   add_right_cancel := by
--     intro a
--     unfold IsAddRightRegular Function.Injective
--     simp
--     exact B2 a
--     intro a1 a2
--     simp

-- instance : AddZeroClass M where
--   zero_add := by
--     intro a
--     rw [<- add_zero_comm]
--     exact B5
-- instance : AddSemigroup M := inferInstance
-- instance : AddMonoid M := inferInstance
-- instance : AddLeftCancelSemigroup M := inferInstance
-- instance : AddLeftCancelMonoid M := inferInstance

end IOPENModel
