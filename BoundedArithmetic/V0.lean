-- This file demonstrates how we can encode the two-sorted logic used for V^0
-- in single-sorted logic modeled by Mathlib.ModelTheory
-- We use the idea described in section 4.5 Single-sorted logic interpretation
-- (Draft p.82 = p.93 of pdf) (draft: https://www.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf)
-- import Init.Notation
import Lean

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
-- import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SimpRw

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Complexity
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.IDelta0
import BoundedArithmetic.Register


-- Syntax for: ∀s X<7, φ X := ∀X:sort, str X -> (len X) < 7 -> φ X

-- `sort` has to be defined above the syntax macros!
-- otherwise, macros expand it to `sort†`
open FirstOrder Language
open HasTypes_is
open HasEmptySet
open HasLen
universe u
variable (num str : Type u)
-- to define Len, Empty etc., we require explicit typing rules
-- along with the object in question!
def Nums := { x : (num ⊕ str) // x.isLeft }
def Strs := { x : (num ⊕ str) // x.isRight }
variable [instNumPeano : peano.Structure (Nums num str)]
variable [instMem : Membership (Nums num str) (Strs num str)]
variable [HasLen (Strs num str) (Nums num str)]
variable [HasEmptySet (Strs num str)]
instance : LT (Nums num str) where
  lt x y := x <= y ∧ x ≠ y


syntax "∃i " Lean.binderIdent ", " term : term
macro_rules
  | `(∃i $x:ident, $p) =>
    `(∃ $x:ident : (Nums num str), $p)

syntax "∃s " Lean.binderIdent ", " term : term
macro_rules
  | `(∃s $x:ident, $p) =>
    `(∃ $x:ident : (Strs num str), $p)

syntax "∀i " Lean.binderIdent ", " term : term
macro_rules
  | `(∀i $x:ident, $p) =>
    `(∀ $x:ident : (Nums num str), $p)

syntax "∀s " Lean.binderIdent ", " term : term
macro_rules
  | `(∀s $x:ident, $p) =>
    `(∀ $x:ident : (Strs num str), $p)

syntax "∃i " Lean.binderIdent binderPred ", " term : term
macro_rules
  | `(∃i $x:ident $pred:binderPred, $p) =>
    `(∃i $x:ident, satisfies_binder_pred% $x $pred ∧ $p)

syntax "∃s " Lean.binderIdent binderPred ", " term : term
macro_rules
  | `(∃s $x:ident $pred:binderPred, $p) =>
    `(∃s $x:ident, satisfies_binder_pred% (len $x) $pred ∧ $p)

syntax "∀i " Lean.binderIdent binderPred ", " term : term
macro_rules
  | `(∀i $x:ident $pred:binderPred, $p) =>
    `(∀i $x:ident, satisfies_binder_pred% $x $pred → $p)

syntax "∀s " Lean.binderIdent binderPred ", " term : term
macro_rules
  | `(∀s $x:ident $pred:binderPred, $p) =>
    `(∀s $x:ident, satisfies_binder_pred% (len $x) $pred → $p)

-- /-- recursive cases (two or more variables): peel the head and recurse on the tail -/
-- -- THIS DOESNT WORK IDK
-- -- macro_rules
-- --   | `(∀i $x:ident $xs:ident, $p) =>
-- --     `(∀ $x:ident : sort, ($x).isLeft -> (∀i $xs*, $p))
-- --   | `(∃i $x:ident $xs:ident+, $p) =>
-- --     `(∃ $x:ident : sort, ($x).isLeft ∧ (∃i $xs*, $p))
-- --   | `(∀s $x:ident $xs:ident+, $p) =>
-- --     `(∀ $x:ident : sort, ($x).isRight -> (∀s $xs*, $p))
-- --   | `(∃s $x:ident $xs:ident+, $p) =>
-- --     `(∃ $x:ident : sort, ($x).isRight ∧ (∃s $xs*, $p))


-- TODO: we can have better syntax for `len x`, but it might require
-- hiding importing of the syntax from mathlib for lattice
-- @[inherit_doc abs]
-- macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)
-- #check |7|
-- instance : Abs (str sort) where


-- typing axioms; 4.5 Single-sorted logic interpretation (Draft p.83 / p.94 of pdf)
class BASIC2Model extends ZambellaModel num str where
  -- axiom for empty string; 4.4.1 Two-Sorted Free Variable Normal Form
  -- E : len (empty : Strs num str).val = (0 : num ⊕ str)
  E {X : Strs num str} (_ : X.val = empty) : len X = (0 : Nums num str)
  B1 : ∀i x,       x + 1 ≠ 0
  B2 : ∀i x, ∀i y, x + 1 = y + 1 -> x = y
  B3 : ∀i x,       x + 0 = x
  B4 : ∀i x, ∀i y, x + (y + 1) = (x + y) + 1
  B5 : ∀i x,       x * 0 = 0
  B6 : ∀i x, ∀i y, x * (y + 1) = (x * y) + x
  B7 : ∀i x, ∀i y, x <= y -> y <= x -> x = y
  B8 : ∀i x, ∀i y, x <= x + y
  B9 : ∀i x,       0 <= x
  B10: ∀i x, ∀i y, x <= y ∨ y <= x
  B11: ∀i x, ∀i y, x <= y <-> x < (y + 1)
  B12: ∀i x,       x ≠ 0 -> (∃i y, (y <= x ∧ (y + 1) = x))
  L1 : ∀s X, ∀i y, y ∈ X -> (y <= (len X) ∧ y ≠ (len X))
  L2 : ∀s X, ∀i y, (y + 1) = len X -> y ∈ X

  SE : ∀s X, ∀s Y,
    len X = len Y (β := Nums num str)
    -> (∀i y, ((y < len X) -> y ∈ X <-> y ∈ Y))
    -> X = Y

namespace BASIC2Model
variable [inst : BASIC2Model num str]

instance : BASICModel (Nums num str) where
  B1 := inst.B1
  B2 := inst.B2
  B3 := inst.B3
  B4 := inst.B4
  B5 := inst.B5
  B6 := inst.B6
  B7 := inst.B7
  B8 := inst.B8

end BASIC2Model


class V0Model extends BASIC2Model num str where
  -- TODO: we can allow some more free vars here, but carefully?
  sigma0B_comp {n1} {a : Type} [IsEnum a]
    (phi : zambella.Formula (((Vars1 n1) ⊕ (Vars1 .y)) ⊕ a)) :
    phi.IsSigma0B -> (mkComprehensionSentence phi).Realize (num ⊕ str)

namespace V0Model
-- TODO: UNIVERSE POLYMORPHISM!
variable [inst : V0Model num str]

open BoundedFormula Formula
open BASIC2Model

omit [HasEmptySet (Strs num str)] in
-- Exercise V.1.1 (a) ¬ x < 0
lemma not_lt_zero : ∀i x, ¬ x < 0 := by
  intro x h
  obtain ⟨h_x_le, h_x_ne⟩ := h
  apply h_x_ne
  apply B7
  · exact h_x_le
  · apply B9

open ZambellaModel

-- Lemma 5.6 (draft, p. 87 / 98 of pdf); V⁰ ⊢ X-MIN
theorem X_MIN : ∀s X > (0 : Nums num str), ∃i x <  len X, x ∈ X ∧ (∀i y < x, ¬ y ∈ X) := by
  -- by Sigma0B-COMP, there is a set Y such that |Y| <= |X| and for all z < |X|,
  -- Y(z) <-> $ Forall x <= z, not X(x)
  -- in the below formulas, `y` has special meaning.
  -- `y` is the length of the ultimate string created

  -- Forall x <= z, x ∉ X
  -- this `X` here is the set from theorem statement, not the `X` created
  -- in the comprehension axiom's internal scope!
  let form1 : zambella.Formula (Vars3 .y .z .X ⊕ Vars1 .x) :=
    (display4 .x (x ∉' X)).flip
  let form2 : zambella.Formula (Vars3 .y .z .X) :=
    Formula.iBdAllNum' z form1
  let form3 : zambella.Formula (Vars1 .z ⊕ Vars2 .y .X) :=
    (display3 .z form2.rotate_213)
  let form4 : zambella.Formula ((Vars1 .z ⊕ Vars1 .y) ⊕ Vars1 .X) :=
    form3.display_swapleft'
  let hcomp := inst.sigma0B_comp form4

  unfold form4 form3 form2 form1 at hcomp
  specialize hcomp (by
    simp only [z, instHasVarVars3_1, x, instHasVarVars4, X, instHasVarVars4_3,
      Sigma0B.display_swapleft', Sigma0B.display3, Sigma0B.rotate_213]
    apply IsSigma0B.bdAll
  )

  simp_comp at hcomp

  intro X X_gt
  -- now, the Y we obtain is exactly the Y from the proof!
  let lenX : Nums num str := len X
  -- set length of string created in comprehension to |X|
  specialize hcomp lenX.val
  sorry
#exit

  -- now destruct Y and strengthen its type from `num ⊕ str` to `Strs num str`
  obtain ⟨Y', h_Y'_le, h_Y'_type, h_Y'_def⟩ := h_comp
  let h_Y'_type' : Y'.isRight := typeStrLift Y' h_Y'_type
  let Y : Strs num str := ⟨Y', h_Y'_type'⟩
  let h_Y_Y' : Y.val = Y' := by unfold Y; simp only

  -- [...] Thus the set Y consists of the numbers smaller than every element in X.
  -- Assuming 0 < |X| [`X_gt`], we will show that |Y| is the least member of X.
  -- Intuitively, this is because |Y| is the least number that is larger than
  -- any member of Y. Formally, we need to show:
  -- (i) X(|Y|)
  -- (ii) ∀ y < |Y|, ¬X(y)
  -- Details are as follows.
  have h_i_iint : (len Y) ∈ X ∧ (∀i t < len Y, t ∉ X) := by
  -- First, suppose that Y is empty.
    by_cases h_Y_empty : Y.val = empty
    · -- Then |Y| = 0 by B12 and L2
      rw [E h_Y_empty]
      constructor; swap
      -- hence (ii) holds vacuously by Exercise V.1.1 (a).
      · intro t h
        exfalso
        apply not_lt_zero (inst := inst)
        exact h
      -- also, X(0) holds, since otherwise Y(0) holds by B7 and B9.
      -- thus we have proved (i)
      · by_contra h_0_not_mem_X
        have zero_in_Y : 0 ∈ Y.val := by
          specialize h_Y'_def 0 (by
            sorry
          )
          -- have h_Y_def' := (Iff.mpr h_Y_def)
          -- problem 1: from comp we get 0 ∈ Y†, but we need 0 ∈ Y!!!!
          rw [h_Y_Y']
          -- TODO: WHY DOES THE BELOW UNFOLD FINISH PROOF???
          -- unfold Membership.mem instMembershipOfStructure.1
          sorry
          -- apply h_Y'_def.mpr
        have zero_lt_len_Y : (0 : Nums num str) < len Y := by
          apply L1
          sorry
        obtain ⟨_, zero_ne_len_Y⟩ := zero_lt_len_Y
        apply zero_ne_len_Y
        rw [E]
        exact h_Y_empty
    -- Now suppose that Y is not empty,
    · -- i.e. Y(y) holds for some y.
      have h_ex_y : ∃y, y ∈ Y := by
        sorry
      obtain ⟨y, hy⟩ := h_ex_y
      -- Then y < |Y| by L1, and thus |Y| ≠ 0 by Exercise V.1.1 (a).
      have lenY_ne_zero : len Y ≠ (0 : Nums num str) := by
        sorry

      -- By B12, |Y| = z + 1 for some z
      obtain ⟨pred_lenY, h_pred_lenY_le, h_pred_lenY_eq⟩ := B12 (len Y) lenY_ne_zero
      -- and hence `Y(z) ∧ ¬Y(z + 1)` by L1 and L2.
      have z_in_Y := L2 Y pred_lenY h_pred_lenY_eq
      have succ_z_notin_Y : (pred_lenY + 1) ∉ Y := by
        sorry

      -- Hence by (50) [i.e. Y_def] we have ∀y ≤ z, ¬X(y)
      have lt_z_then_notin_X : ∀y ≤ pred_lenY, y ∉ X := by
        sorry

      -- ... ∧ ∃i ≤ (z + 1), X(i).
      -- It follows that `i = z + 1` in the second conjunct,
      -- since if `i < z + 1` then `i ≤ z` by B11,
      -- which contradicts the first conjunct

      -- This establishes (i) and (ii), since `i = z + 1 = |Y|`.
      constructor
      · sorry
      · rw [<- h_pred_lenY_eq]
        conv => right; lhs; rw [<- B11]
        exact lt_z_then_notin_X

  -- now, finish the proof!
  have ⟨h_len_Y_mem_X, h_len_Y_is_min⟩ := h_i_iint

  exists (len Y)
  constructor
  · apply L1 X (len Y) h_len_Y_mem_X
  · constructor
    · apply h_len_Y_mem_X
    · apply h_len_Y_is_min




-- Corollary V.1.7. V⁰ ⊢ X-IND
-- TODO: TO EXTRACT CODE FROM V⁰,
--       WE CAN'T DO THIS PROOF BY CONTRADICTION!!!!
theorem X_IND :
  ∀i z, ∀s X_,
  0 ∈ X_
  -> (∀i y < z, (y ∈ X_ -> (y + 1) ∈ X_))
  -> z ∈ X_ := by
  -- We prove by contradiction. Assume ¬X-IND,
  -- then we have for some `z`, ...
  intro z_ X_ h_base h_step
  by_contra h_z_notin_X

  -- By comp, there is a set Y with |Y| ≤ z + 1 such that
  -- ∀y < (z + 1), (y ∈ Y ↔ y ∉ X)
  let formula : zambella.Formula (Vars1X ⊕ Vars2yz) :=
    (display_X_yzX $ z ∉' X)
  let h_comp := inst.sigma0B_comp formula (disp := Vars1X) (by
    sorry
  )

  conv at h_comp =>
    unfold formula Sentence.Realize Formula.Realize mkComprehensionSentence
    unfold iAlls' alls alls
    simp only [realize_all]
    intro;
    simp only [BoundedFormula.realize_relabel]
    unfold Formula.flip
    simp only [BoundedFormula.realize_relabelEquiv]
    unfold mkInl
    simp only [BoundedFormula.realize_relabelEquiv]
    unfold iBdEx' iExs' exs exs
    simp only [realize_ex]; right; intro
    simp only [BoundedFormula.realize_relabel]
    simp only [BoundedFormula.realize_inf]
    conv =>
      left
      simp only [y, HasVar_y.y, Term.relabel.eq_1, Sum.map_inl, IsEnum.size.Vars1X,
        IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero,
        Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, Term.realize_le, Term.realize_var,
        Sum.elim_inl, Function.comp_apply, Sum.map_inr, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero,
        lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq, id_eq, Sum.swap_inl,
        IsEnum.toIdx.Vars1y_y, Fin.isValue]
    conv =>
      right
      simp only [BoundedFormula.realize_relabelEquiv]
      unfold display_X_yX
      simp only [BoundedFormula.realize_relabelEquiv]
      unfold iBdAllLt'
      unfold iAlls' alls alls
      simp only [BoundedFormula.realize_inf]
      conv =>
        left
        simp only [X, instHasVar_XVars2yX, IsEnum.size.Vars1X, IsEnum.size.Vars1y, Nat.add_zero,
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
          Equiv.coe_fn_mk, BoundedFormula.realize_rel₁, Term.realize_var, Sum.elim_inl,
          Function.comp_apply, Sum.swap_inl, Sum.map_inr, IsEnum.toIdx.Vars1X, Fin.isValue,
          Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
          cast_eq]
      conv =>
        right
        simp only [realize_all]; intro;
        simp only [BoundedFormula.realize_relabel]
        simp only [BoundedFormula.realize_imp]
        conv =>
          left
          simp only [Term.lt, instHasDisplayedVars1z, y, instHasVar_yVars2yX, Term.relabel.eq_1,
            Sum.map_inl, instHasDisplayedVars1z.eq_1, IsEnum.size.Vars1z, IsEnum.size.Vars1X,
            IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero,
            Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, BoundedFormula.realize_inf,
            Term.realize_le, Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.map_inr,
            IsEnum.toIdx.Vars1z_z, Fin.isValue, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero,
            lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq, id_eq, Sum.swap_inr,
            Sum.swap_inl, IsEnum.toIdx.Vars1y_y, BoundedFormula.realize_not]
        conv =>
          right
          unfold display_z_yzX
          simp only [BoundedFormula.realize_relabelEquiv]
          simp only [BoundedFormula.realize_iff, Term.in]
          conv =>
            left
            simp only [z, instHasVar_zVars3yzX, X, instHasVar_XVars3yzX, instHasDisplayedVars1z,
              IsEnum.size.Vars1z, IsEnum.size.Vars1X, IsEnum.size.Vars1y, Nat.add_zero,
              Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
              Equiv.coe_fn_mk, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inl,
              Function.comp_apply, Sum.swap_inl, Sum.map_inr, IsEnum.toIdx.Vars1z_z, Fin.isValue,
              Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte,
              Fin.reduceLast, cast_eq, Sum.swap_inr, Sum.map_inl, id_eq, IsEnum.toIdx.Vars1X]
          conv =>
            right
            simp only [BoundedFormula.realize_subst]
            unfold alls
            simp only [BoundedFormula.realize_all]; intro; intro
            simp only [BoundedFormula.realize_relabel]
            unfold alls
            unfold display_X_yzX
            simp only [BoundedFormula.realize_relabelEquiv]
            simp only [Term.notin, Term.in, z, instHasVar_zVars3yzX, X, instHasVar_XVars3yzX,
              IsEnum.size.Vars2yz, instHasDisplayedVars1z, IsEnum.size.Vars1z, IsEnum.size.Vars1X,
              IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
              Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, Term.realize_var,
              Function.comp_apply, Sum.swap_inl, Sum.map_inr, IsEnum.toIdx.Vars1z_z, Fin.isValue,
              Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte,
              Fin.reduceLast, cast_eq, BoundedFormula.realize_not, BoundedFormula.realize_rel₂,
              Sum.elim_inl, IsEnum.toIdx.Vars2yz_z, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Sum.map_inl,
              id_eq]

  -- recall: By comp, there is a set Y with |Y| ≤ z + 1 such that
  -- ∀y < (z + 1), (y ∈ Y ↔ y ∉ X)
  specialize h_comp (z_ + (1 : Nums num str)).val
  obtain ⟨Y', h_lenY'_le, h_Y'_type, h_Y'_def⟩ := h_comp
  let h_Y'_type' : Y'.isRight := typeStrLift Y' h_Y'_type
  let Y : Strs num str := ⟨Y', h_Y'_type'⟩
  let h_Y_Y' : Y.val = Y' := by unfold Y; simp only

  -- Then Y(z) holds by Exercise V.1.1 (b), ...
  have h_z_in_Y : z_ ∈ Y := by sorry
  -- ... so 0 < |Y| by (a) and L1.
  have zero_lt_lenY : (0 : Nums num str) < len Y := by sorry

  -- By Y-MIN, Y has a least element y₀.
  obtain ⟨minY, h_minY_lt, h_minY_in, h_minY_def⟩ := X_MIN num str Y zero_lt_lenY

  -- Then y₀ ≠ 0 because X(0), ...
  have h_minY_ne_zero : minY ≠ (0 : Nums num str) := by sorry

  -- ... hence y₀ = x₀ + 1 for some x₀, by B12.
  obtain ⟨pred_minY, h_pred_minY_le, h_pred_minY_eq⟩ := B12 minY h_minY_ne_zero

  -- But then we must have X(x₀) and ¬X(x₀ + 1),...
  have h_pred_minY_in_X : pred_minY ∈ X_ := by sorry
  have h_minY_notin_X : minY ∉ X_ := by sorry

  -- ... which contradicts our assumption
  -- specifically:
  -- h_z_notin_X : z_ ∉ X_
  -- h_step : ∀ y < z_, y ∈ X_ → y + 1 ∈ X_
  specialize h_step pred_minY (by
    -- prove that pred_minY < z_
    -- h_lenY'\_le : Y' ≤ ↑(z_ + 1)
    -- h_z_in_Y : z_ ∈ Y
  sorry)
  apply h_minY_notin_X
  rw [<- h_pred_minY_eq]
  apply h_step
  exact h_pred_minY_in_X


-- open Mathlib Tactic
-- #check Mathlib.Tactic.tacticSimp_rw___

-- Corollary V.1.8 If V⁰ proves Φ-COMP, then V⁰ proves Φ-IND, MIN, MAX
-- we limit to Φ := Sigma B0
theorem sigma0B_ind {disp} [HasDisplayed disp] {a} [IsEnum a]
  (phi : zambella.Formula (disp ⊕ a)) :
  phi.IsSigma0B
  -> (mkInductionSentenceTyped phi).Realize (num ⊕ str) :=
by
  -- technicality: we can't simplify in this theorem,
  -- as the size of `a` is unknown and trying to make induction on
  -- the size or something is very difficult, as Lean can't
  -- tell that in `motive`, the equality holds and detects some types
  -- as unequal...
  intro h_sigma0B
  unfold mkInductionSentenceTyped
  -- we prove `forall z, φ(z)`. here we intro `z`.
  intro base step z

  conv =>
    rw [BoundedFormula.realize_relabel]
    unfold Formula.flip
    rw [BoundedFormula.realize_relabelEquiv]
    unfold display
    rw [BoundedFormula.realize_relabelEquiv]
    unfold IsNum
    unfold toFormula'
    rw [BoundedFormula.realize_imp]
    simp only [hasDispIsEnum.eq_1, Fin.isValue, Nat.add_zero, Nat.reduceAdd, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, BoundedFormula.realize_rel₁,
      Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.swap_inl, Sum.map_inr, Sum.elim_inr,
      Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq]

  intro h_z_type

  -- lift type of z using embedded type information `htype`
  let h_z_type' : z.isLeft := typeNumLift z h_z_type
  let z' : Nums num str := ⟨z, h_z_type'⟩
  let h_z_z' : z'.val = z := by unfold z'; simp only

  -- By Φ-COMP, there exists X such that |X| ≤ z + 1 and
  -- ∀y < (z + 1), (X(y) ↔ φ(y))
  let comp := inst.sigma0B_comp phi h_sigma0B

  conv at comp =>
    simp only
    unfold mkComprehensionSentence Sentence.Realize Formula.Realize
    unfold iAlls' alls alls
    rw [realize_all]
    intro
    rw [BoundedFormula.realize_relabel]
    unfold Formula.flip
    rw [BoundedFormula.realize_relabelEquiv]
    unfold mkInl
    rw [BoundedFormula.realize_relabelEquiv]
    unfold iBdEx' iExs' exs exs
    rw [BoundedFormula.realize_ex]
    rhs; intro
    rw [BoundedFormula.realize_relabel]
    rw [BoundedFormula.realize_inf]
    conv =>
      left
      simp only [y, instHasVar_yVars1y, Term.relabel.eq_1, Sum.map_inl, hasDispIsEnum.eq_1,
        Fin.isValue, IsEnum.size.Vars1X, IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one,
        Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk,
        Term.realize_le, Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.map_inr,
        Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
        cast_eq, id_eq, Sum.swap_inl, IsEnum.toIdx.Vars1y_y]
    conv =>
      right
      rw [BoundedFormula.realize_relabelEquiv]
      unfold display_X_yX
      rw [BoundedFormula.realize_relabelEquiv]
      rw [BoundedFormula.realize_inf]
      conv =>
        left
        simp only [X, instHasVar_XVars2yX, hasDispIsEnum.eq_1, Fin.isValue, IsEnum.size.Vars1X,
          IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero,
          Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, BoundedFormula.realize_rel₁,
          Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.swap_inl, Sum.map_inr,
          Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
          cast_eq]

      conv =>
        right
        unfold iBdAllLt' iAlls' alls alls
        rw [BoundedFormula.realize_all]; intro
        rw [BoundedFormula.realize_relabel]
        rw [BoundedFormula.realize_imp]
        conv =>
          left
          simp [delta0_simps]
          unfold Term.lt
          simp only [Fin.isValue, BoundedFormula.realize_inf, Term.realize_le, Term.realize_var,
            Sum.elim_inl, Function.comp_apply, Sum.map_inr, Sum.elim_inr, Fin.snoc, Nat.reduceAdd,
            Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq, Sum.map_inl,
            id_eq, Sum.swap_inr, Sum.swap_inl, IsEnum.toIdx.Vars1y_y, BoundedFormula.realize_not]
        conv =>
          right
          unfold display_z_yzX
          rw [BoundedFormula.realize_relabelEquiv]
          rw [BoundedFormula.realize_relabelEquiv]
          rw [BoundedFormula.realize_iff]
          conv =>
            left
            unfold Term.in
            simp only [Language.z, instHasVar_zVars3yzX, X, instHasVar_XVars3yzX,
              instHasDisplayedVars1z.eq_1, hasDispIsEnum.eq_1, Fin.isValue, IsEnum.size.Vars1z,
              IsEnum.size.Vars1X, IsEnum.size.Vars1y, Nat.add_zero, Nat.succ_eq_add_one,
              Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk,
              BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inl, Function.comp_apply,
              Sum.swap_inl, Sum.map_inr, Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false,
              ↓reduceDIte, Fin.reduceLast, cast_eq, Sum.swap_inr, Sum.map_inl, id_eq]
          conv =>
            right
            simp only [Nat.add_zero, instHasDisplayedVars1z.eq_1, hasDispIsEnum.eq_1, Fin.isValue,
              IsEnum.size.Vars1z, IsEnum.size.Vars1X, IsEnum.size.Vars1y, Nat.succ_eq_add_one,
              Nat.reduceAdd, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk,
              realize_subst, Term.realize_var, Function.comp_apply, Sum.swap_inl, Sum.map_inr,
              Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte,
              Fin.reduceLast, cast_eq]

  -- recall: By Φ-COMP, there exists X such that |X| ≤ z + 1 and
  -- ∀y < (z + 1), (X(y) ↔ φ(y))
  specialize comp z -- should be `z` and not `(z + 1)` i think
  obtain ⟨X, h_X_le, h_X_type, h_X_def⟩ := comp
  -- lift type of `X` using embedded type information `htype`
  let h_X_type' : X.isRight := typeStrLift X h_X_type
  let X' : Strs num str := ⟨X, h_X_type'⟩
  let h_X_X' : X'.val = X := by unfold X'; simp only

  -- By B11, Exercise V.1.1 (c,e) and (51) [`base ∧ step`] we conclude from this
  have base_X : 0 ∈ X := by
    specialize h_X_def 0 (by
      -- 0 <= z ∧ ¬ z <= 0
      constructor
      · sorry
      · sorry
    )
    unfold Membership.mem instMembershipOfStructure
    simp only
    apply h_X_def.mpr

    -- we need to show that `base` is actually the target........
    -- revert and intro so that it's easy to see and compare both
    revert base
    intro base

    conv at base =>
      rw [realize_subst]
      conv =>
        arg 1; arg 1
        unfold alls
      unfold iAlls' alls alls
      conv =>
        arg 2
        simp only [realize_zero_to_zero]
      simp only [Nat.add_zero]
    convert base

  have step_X : ∀ y < z, y.isLeft -> y ∈ X -> (y + 1) ∈ X := by
    intro y h_yz h_ytype h_yX

    -- simplify goal
    have h_X_def_y := h_X_def y (by
      -- y + 1 ≤ z ∧ ¬z ≤ y + 1
      sorry
    )
    have h_X_def_ysucc := h_X_def (y + 1) (by
      -- y + 1 ≤ z ∧ ¬z ≤ y + 1
      sorry
    )
    rw [Membership.mem, instMembershipOfStructure]
    simp only
    rw [h_X_def_ysucc]

    -- now try to apply step
    specialize step y
    conv at step =>
      rw [BoundedFormula.realize_relabel]
      unfold Formula.flip
      rw [BoundedFormula.realize_relabelEquiv]
      unfold display
      unfold toFormula'
      rw [BoundedFormula.realize_relabelEquiv]
      unfold IsNum
      rw [BoundedFormula.realize_imp]
      rw [BoundedFormula.realize_imp]

    -- prove typing rule of step
    specialize step (by
      simp only [hasDispIsEnum.eq_1, Fin.isValue, Nat.add_zero, Nat.reduceAdd, Fin.castAdd_zero,
        Fin.cast_refl, Function.comp_id, Equiv.coe_fn_mk, BoundedFormula.realize_rel₁,
        Term.realize_var, Sum.elim_inl, Function.comp_apply, Sum.swap_inl, Sum.map_inr,
        Sum.elim_inr, Fin.snoc, Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast,
        cast_eq]
      sorry
    )

    -- prove precondition of step
    specialize step (by
      -- unfold IsNum
      -- intro
      conv at h_yX =>
        rw [Membership.mem, instMembershipOfStructure]
        simp only
      rw [h_X_def_y] at h_yX

      convert h_yX
      unfold iAlls'
      conv =>
        lhs
        unfold alls alls
      rfl
    )

    -- match with the postcondition of step!
    conv at step =>
      rw [realize_subst]
      unfold iAlls'
      simp [delta0_simps]

    unfold alls at step
    unfold alls at step

    convert step


  -- recall: By B11, Exercise V.1.1 (c,e) and (51) [`base ∧ step`]
  -- we conclude from this X(0) ∧ ∀ y < z, (X(y) -> X(y + 1))
  -- Finally X(z) follows from this and X-IND, ...
  -- careful! out `Membership` is on Strs num str, not on str..
  let X' : Strs num str := ⟨X, typeStrLift X h_X_type⟩
  have h_z_in_X := X_IND num str z' X'

  -- conv at h_z_in_X =>
  --   conv => left; rw [memLift]
  --   conv => right; left; right; rw [memLift]
  --   conv => right; right; rw [memLift]
  simp_rw [memLift] at h_z_in_X
  -- specialize h_z_in_X base_X
  -- ... and so φ(z) follows from (52) [`X_def`] and Exercise V.1.1 (b)
  sorry


-- Theorem V.1.9. V⁰ is a conservative extension of IΔ₀
-- instance [h : V0Model num str] : IDelta0Model num where
--   funMap {n_args} f args :=
--     match f with
--     | PeanoFunc.zero => (h.funMap ZambellaFunc.zero args) ∘ (fun n => Sum.inl (β := str) n))




end V0Model







-- -- we need to prove add_assoc -> zero_add_comm -> zero_add
-- -- in order to prove the C axiom for BASIC
-- theorem add_assoc
--   : ∀ x y z : M, (x + y) + z = x + (y + z) :=
-- by
--   -- the below block is a set of repetitive conversion we need to do;
--   -- this should be automatized by a single tactic
--   have ind := open_induction (self := iopen)
--     (display_z_xyz  $ ((x + y) + z) =' (x + (y + z)))
--   simp only [delta0_simps] at ind
--   specialize ind trivial
--   -- now, we cannot simply do `apply ind` without `intros`,
--   -- because our induction formula has a different order of quantifiers;
--   -- Lean can't unify ∀x y, phi(x, y) with ∀y x, phi(x, y)
--   -- see also: refer to Mathlib.Logic.Basic.forall_swap
--   intros
--   apply ind ?base ?step
--   clear ind
--   · intro x y
--     rw [B3 (x + y)]
--     rw [B3 y]
--   · intro z hInd x y
--     rw [B4]
--     rw [B4]
--     rw [B4]
--     rw [<- (B2 (x + y + z) (x + (y + z)))]
--     rw [hInd]
