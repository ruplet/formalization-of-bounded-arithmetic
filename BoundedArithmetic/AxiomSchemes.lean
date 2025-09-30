import Mathlib.ModelTheory.Syntax

import BoundedArithmetic.IsEnum
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Syntax

open FirstOrder Language BoundedFormula


-- i think that type level is set to 0 because of
-- Vars1x type is just Type
variable {α disp : Type}

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)
-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
def mkInductionSentence {n} {a} [IsEnum a] {disp} [HasDisplayed disp]
  (phi: peano.BoundedFormula (disp ⊕ a) n)
  : peano.Sentence :=
  let univ := phi.alls.iAlls'

  let base := univ.subst (fun _ => 0)

  let step_assumption := univ
  let step_target := univ.subst (fun _ => (var HasDisplayed.fv) + 1)
  let step' : peano.Formula disp := step_assumption ⟹ step_target
  let step := step'.display.flip.iAlls'

  let forall_x_holds := univ.display.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds


-- Definition V.I.2 (Comprehension Axiom); p. 96 PDF; release of Logical Foundations
-- `X` cannot occur free in `phi(z)`, but `y` can
def mkComprehensionSentence {n} {a} [IsEnum a]
  (phi: zambella.BoundedFormula (Vars2yz ⊕ a) n)
  : zambella.Sentence :=
  -- free vars of `phi` need to be quantifier with outermost quantifier!
  -- X(z) iff phi(z)
  -- let phi_z := display_z_yz phi
  sorry

-- sigma0B_comp {n} :
--     ∀ (phi_syntax : Lang.BoundedFormula Empty (n + 1)),
--     IsSigma0B phi_syntax ->
--     -- X must not occur free in phi(z); 1 is deBruijn index for second-shallowest quantifier
--     -- no_free 1 phi_syntax ->
--     -- ∀ y ∃ X <= y ∀ z < y, (z ∈ X ↔ φ(z))
--     forall n_free_vars : Fin (n - 2) -> sort,
--     (
--     forall y : sort,
--       int y ->
--       (∃ X : sort, isStr X ∧ leq (len X) y ∧
--         (∀ z : sort,
--           int z ->
--           ((leq z y ∧ z ≠ y) ->
--             (
--               mem z X ↔
--               @phi_syntax.Realize
--                 Lang
--                 sort
--                 (TwoSortedBASICModel_Structure toTwoSortedBASICModel)
--                 _ _ (Empty.elim)
--                 (fun (idx : Fin (n + 1)) =>
--                   let free_vars := List.ofFn n_free_vars ++ [z, X, y]
--                   -- let free_vars := [z, X, y] ++ List.ofFn n_free_vars
--                   have h2 : (n + 1) <= free_vars.length := by
--                     unfold free_vars
--                     simp
--                     match n with
--                     | 0 => simp
--                     | 1 => simp
--                     | k + 2 => simp
--                   have idx_cast : Fin free_vars.length := Fin.castLE h2 idx
--                   List.get free_vars idx_cast
--                 )
--           )
--         )
--       )
--     )
--     )


-- def num_induction_on
--   {motive : M -> Sort*}
--   (x : M)
--   (h0 :  motive 0)
--   (hs : motive 0 -> forall n, motive n -> motive (n + 1))
--   (ind_valid : motive 0 -> (∀n, motive n -> motive (n + 1)) -> ∀ n, motive n)
--   : motive x :=
-- by
--   apply ind_valid
--   apply h0
--   apply (hs h0)
