import Mathlib.ModelTheory.Syntax

import BoundedArithmetic.IsEnum
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.Syntax

open FirstOrder Language


-- i think that type level is set to 0 because of
-- Vars1x type is just Type
variable {α disp : Type}

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)
-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
def mkInductionSentence {n} {a} [IsEnum a] {disp} [HasDisplayed disp] (phi: peano.BoundedFormula (disp ⊕ a) n) : peano.Sentence :=
  let univ := phi.alls.iAlls'

  let base := univ.subst (fun _ => 0)

  let step_assumption := univ
  let step_target := univ.subst (fun _ => (var HasDisplayed.fv) + 1)
  let step' : peano.Formula disp := step_assumption ⟹ step_target
  let step := step'.display.flip.iAlls'

  let forall_x_holds := univ.display.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds



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
