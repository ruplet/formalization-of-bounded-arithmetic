-- This file demonstrates how we can encode the two-sorted logic used for V^0
-- in single-sorted logic modeled by Mathlib.ModelTheory
-- We use the idea described in section 4.5 Single-sorted logic interpretation
-- (Draft p.82 = p.93 of pdf) (draft: https://www.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf)
-- import Init.Notation
import Lean

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.Linarith

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Complexity
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.IDelta0


-- Syntax for: ∀s X<7, φ X := ∀X:sort, str X -> (len X) < 7 -> φ X

-- `sort` has to be defined above the syntax macros!
-- otherwise, macros expand it to `sort†`
open FirstOrder Language zambella
open zambella.HasTypes_is
open HasEmptySet
open HasLen
universe u
variable (num str : Type u)
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
class BASIC2Model extends zambella.Structure (num ⊕ str) where
  -- assert that typing rules match
  typeStrLift :
    ∀ t : (num ⊕ str),
    (RelMap ZambellaRel.isstr ![t]) -> t.isRight

  -- axiom for empty string; 4.4.1 Two-Sorted Free Variable Normal Form
  E : len (empty : num ⊕ str) = (0 : num ⊕ str)
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
  B11: ∀i x, ∀i y, x <= y <-> (x <= (y + 1) ∧ x ≠ (y + 1))
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
  -- {a} [IsEnum a]
  sigma0B_comp {disp} [HasDisplayed disp]
    (phi : zambella.Formula (disp ⊕ Vars2yz)) :
    phi.IsSigma0B -> (mkComprehensionSentence phi).Realize (num ⊕ str)

namespace V0Model
-- TODO: UNIVERSE POLYMORPHISM!
variable [inst : V0Model.{_, 0} num str]

open BoundedFormula Formula
open BASIC2Model

-- Lemma 5.6 (draft, p. 87 / 98 of pdf); V⁰ ⊢ X-MIN
theorem xmin : ∀s X > (0 : Nums num str), ∃i x <  len X, x ∈ X ∧ (∀i y < x, ¬ y ∈ X) := by
  -- by Sigma0B-COMP, there is a set Y such that |Y| <= |X| and for all z < |X|,
  -- Y(z) <-> $ Forall y, y <= z -> not X(y)

  -- in the below formula, `y` and `z` variables have special meaning.
  -- `y` is the length of the ultimate string created
  let form1 : zambella.Formula (Vars2yzX ⊕ Vars1x) :=
    (display_x_xyzX (x ∉' X)).flip
  let form2 : zambella.Formula Vars2yzX :=
    Formula.iBdAll' z form1
  let formula : zambella.Formula (Vars1X ⊕ Vars2yz) :=
    (display_X_yzX form2)

  -- (a := Vars1X) is necessary for universe polymorphism fix
  -- (instance finding)
  let h_comp := inst.sigma0B_comp formula (disp := Vars1X) (by
    unfold formula display_X_yzX
    rw [Sigma0B.relabelEquiv]
    unfold form2
    -- there is something fucked up in this constructor
    -- apply IsSigma0B.bdAll
    sorry
  )

  conv at h_comp =>
    unfold formula Sentence.Realize Formula.Realize mkComprehensionSentence
    unfold iAlls' alls alls
    simp only [realize_all];
    intro;
    simp only [BoundedFormula.realize_relabel]
    unfold BoundedFormula.flip
    simp only [BoundedFormula.realize_relabelEquiv]
    unfold mkInl
    simp only [BoundedFormula.realize_relabelEquiv]
    unfold iBdEx' iExs' exs exs
    simp only [realize_ex]; right; intro
    simp only [BoundedFormula.realize_relabel]
    simp only [BoundedFormula.realize_inf]
    conv =>
      left
      simp [delta0_simps, HasVar_y.y]
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
        simp [delta0_simps]
      conv =>
        right
        simp only [realize_all]; intro;
        simp only [BoundedFormula.realize_relabel]
        simp only [BoundedFormula.realize_imp]
        conv =>
          left
          simp [Term.lt, delta0_simps]
        conv =>
          right
          unfold display_z_yzX
          simp only [BoundedFormula.realize_relabelEquiv]
          simp only [BoundedFormula.realize_iff, Term.in]
          conv =>
            left
            simp [delta0_simps]
          conv =>
            right
            simp only [BoundedFormula.realize_subst]
            unfold alls
            simp only [BoundedFormula.realize_all]; intro; intro
            unfold form2 iBdAll' iAlls' alls alls alls display_X_yzX
            simp only [BoundedFormula.realize_all]
            simp only [BoundedFormula.realize_relabel]
            simp only [BoundedFormula.realize_relabelEquiv]
            simp only [BoundedFormula.realize_all]; intro
            simp only [BoundedFormula.realize_relabel]
            simp only [BoundedFormula.realize_imp]
            conv =>
              left; simp [delta0_simps]
            conv =>
              right;
              unfold form1
              simp [delta0_simps, Term.notin, Term.in]

  intro X X_gt
  -- now, the Y we obtain is exactly the Y from the proof!
  let lenX : Nums num str := len X
  -- set length of string created in comprehension to |X|
  specialize h_comp lenX.val

  -- now destruct Y and strengthen its type from `num ⊕ str` to `Strs num str`
  obtain ⟨Y, h_Y_le, h_Y_type, h_Y_def⟩ := h_comp
  have h_Y_type' : Y.isRight := typeStrLift Y h_Y_type
  have Y : Strs num str := ⟨Y, h_Y_type'⟩
  clear h_Y_type h_Y_type'

  -- [...] Thus the set Y consists of the numbers smaller than every element in X.
  -- Assuming 0 < |X| [h_X_len_pos], we will show that |Y| is the least member of X.
  -- Intuitively, this is because |Y| is the least number that is larger than
  -- any member of Y. Formally, we need to show:
  -- (i) X(|Y|)
  -- (ii) ∀ y < |Y|, ¬X(y)
  -- Details are as follows.
  have h_i_iint : (len Y) ∈ X ∧ (∀i t < len Y, t ∉ X) := by
  -- First, suppose that Y is empty.
    if h_Y_empty : Y = empty then {
      constructor
      rw [h_Y_empty]
      -- FROM NOW ON SIE PIERDOLI! COS SIE TYPY NIE ZGADZAJA I RW NIE IDZIE
      #check E (self := inst.toBASIC2Model)
      conv => arg 2; rw [E (self := inst.toBASIC2Model)]
      by_contra h_0_not_mem_X
      -- prove (i) X(|Y|)
      · -- from definition of Y, having the assumption (contradictory) that
        -- 0 is not in X, try to obtain element of Y. since Y empty, contr.
        -- specialize h_Y_content M.0 M.TypeZero ?_ ?_
        -- prove 0 <= |X|
        · unfold TwoSortedBASICModel.lt at h_X_len_pos
          obtain ⟨h_X_len_leq_0, _ ⟩ := h_X_len_pos
          apply (h_X_len_leq_0)
        -- prove 0 ≠ |X|
        · unfold TwoSortedBASICModel.lt at h_X_len_pos
          obtain ⟨_, h_X_len_neq_0⟩ := h_X_len_pos
          apply (h_X_len_neq_0)
        -- now in h_Y_content we should have something of the form:
        -- forall a, int a -> leq a 0 -> ¬ mem a X
        have Yc' := (Iff.mpr h_Y_content)
        -- have h_0_not_mem_Y : ¬ M.mem M.0 Y := by
          intro h_0_mem_Y
          -- have ⟨_, h_0_neq_len_Y⟩ := M.L1 Y M.0 h_Y_type M.TypeZero h_0_mem_Y
          apply h_0_neq_len_Y
          rw [h_Y_empty]
          rw [M.E]
        apply h_0_not_mem_Y
        apply Yc'
        intro a h_a_type h_a_leq_0 h_a_mem_X
        apply h_0_not_mem_X
        -- now, prove that a = 0
        -- have h_a_eq_0 : a = M.0 := by
          -- apply M.B7 a M.0 h_a_type M.TypeZero
          · exact h_a_leq_0
          · apply M.B9 a h_a_type
        rw [h_a_eq_0] at h_a_mem_X
        exact h_a_mem_X
      -- prove (ii) ∀ y < |Y|, ¬X(y)
      · intro t h_t_type h_t_lt_len_Y h_t_mem_X
        rw [h_Y_empty] at h_t_lt_len_Y
        rw [M.E] at h_t_lt_len_Y
        obtain ⟨h_t_leq_0, h_t_neq_0⟩ := h_t_lt_len_Y
        apply h_t_neq_0
        -- apply M.B7 t M.0 h_t_type M.TypeZero
        apply h_t_leq_0
        apply M.B9 t h_t_type
    } else {
      -- Now suppose that Y is not empty, i.e. Y(y) holds for some y.
      -- ...
      sorry
    }

  -- now, finish the proof!
  have ⟨h_len_Y_mem_X, h_len_Y_is_min⟩ := h_i_ii
  clear h_i_ii

  exists (M.len Y)
  refine ⟨?_, ?_, ?_⟩
  · apply M.L1 X (M.len Y) h_X_type (M.TypeLen Y h_Y_type) h_len_Y_mem_X
  · apply h_len_Y_mem_X
  · apply h_len_Y_is_min


end V0Model





-- Theorem V.1.9. V⁰ is a conservative extension of IΔ₀

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



#exit

@[simp] def realize_at : forall {n}, (sort : TwoSortedBASICModel) -> Lang.BoundedFormula Empty (n + 1) -> M.sort -> Prop
| 0, M, phi, term => @phi.Realize Lang M.sort (TwoSortedBASICModel_Structure sort) _ _ (Empty.elim) ![term]
| _ + 1, M, phi, term => realize_at sort phi.all term

-- TODO: DEBRUIJN: here I assumed 0 deBruijn index is the closest quantifier. but this does not seem to be right!
-- for now, I changed 0 to n
inductive IsSigma0B : {n : Nat} -> Lang.BoundedFormula Empty n -> Prop
| of_isQF {phi} (h : BoundedFormula.IsQF phi) : IsSigma0B phi
-- bounded number quantifiers are allowed
| bdNumEx  {n} {phint : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi):  IsSigma0B $ ex_form $ and_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)
| bdNumAll {n} {phint : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi) : IsSigma0B $ all_form $ imp_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)
-- enable optional type implication
| bdNumAll' {n} {phint : Lang.BoundedFormula Empty (n + 1)} (t : Lang.Term (Empty ⊕ Fin (n + 1))) (h : IsSigma0B phi) : IsSigma0B $ all_form $ imp_form (i_form (var_term (Fin.ofNat (n + 1) n))) $ imp_form (leq_form (var_term (Fin.ofNat (n + 1) n)) (t)) (phi)

def TwoSortedBASICModel.lt (sort : TwoSortedBASICModel) (x y : M.sort) : Prop :=
  M.leq x y ∧ x ≠ y

-- p. 87 Draft (98 of pdf)
structure V0Model extends TwoSortedBASICModel where
  sigma0B_comp {n} :
    ∀ (phi_syntax : Lang.BoundedFormula Empty (n + 1)),
    IsSigma0B phi_syntax ->
    -- X must not occur free in phi(z); 1 is deBruijn index for second-shallowest quantifier
    -- no_free 1 phi_syntax ->
    -- ∀ y ∃ X <= y ∀ z < y, (z ∈ X ↔ φ(z))
    forall n_free_vars : Fin (n - 2) -> sort,
    (
    forall y : sort,
      int y ->
      (∃ X : sort, isStr X ∧ leq (len X) y ∧
        (∀ z : sort,
          int z ->
          ((leq z y ∧ z ≠ y) ->
            (
              mem z X ↔
              @phi_syntax.Realize
                Lang
                sort
                (TwoSortedBASICModel_Structure toTwoSortedBASICModel)
                _ _ (Empty.elim)
                (fun (idx : Fin (n + 1)) =>
                  let free_vars := List.ofFn n_free_vars ++ [z, X, y]
                  -- let free_vars := [z, X, y] ++ List.ofFn n_free_vars
                  have h2 : (n + 1) <= free_vars.length := by
                    unfold free_vars
                    simp
                    match n with
                    | 0 => simp
                    | 1 => simp
                    | k + 2 => simp
                  have idx_cast : Fin free_vars.length := Fin.castLE h2 idx
                  List.get free_vars idx_cast
                )
          )
        )
      )
    )
    )

instance V0Model_Structure (sort : V0Model) : Lang.Structure M.sort :=
{
  funMap := fun {arity} f =>
    match arity, f with
    | 0, V0Func.0 => fun _ => M.0
    | 0, V0Func.1 => fun _ => M.1
    | 0, V0Func.empty => fun _ => M.empty
    | 1, V0Func.len => fun args => M.len (args 0)
    | 2, V0Func.=> + fun args => M.( +args 0) (args 1)
    | 2, V0Func.mul => fun args => M.mul (args 0) (args 1)

  RelMap := fun {arity} r =>
    match arity, r with
    | 1, V0Rel.int => fun args => M.(args 0).isLeft
    | 1, V0Rel.isStr => fun args => M.isStr (args 0)
    | 2, V0Rel.leq => fun args => M.leq (args 0) (args 1)
    | 2, V0Rel.mem => fun args => M.mem (args 0) (args 1)
}
