import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.IsEnum
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Syntax
import BoundedArithmetic.Order

open FirstOrder Language BoundedFormula Formula


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
def mkComprehensionSentence {n} {a} [IsEnum a] {disp} [HasDisplayed disp]
  (phi: zambella.BoundedFormula (disp ⊕ a) n)
  : zambella.Sentence :=
    let univ := phi.alls.iAlls'

    -- X(z) ↔ φ(z)
    let iff : zambella.Formula Vars2yzX :=
      z ∈' X ⇔ univ.subst (fun _ => zambella.var .z)
    let all_z : zambella.Formula Vars2yX := iBdAllLt' y (display_z_yzX iff).flip
    -- TODO: UNIVERSE POLYMORPHISM
    let X_type : zambella.Formula.{0, 0} Vars2yX := Relations.boundedFormula₁ ZambellaRel.isstr X
    let ex_X : zambella.Formula _ := iBdEx' y (display_X_yX (X_type ⊓ all_z)).flip

    -- quantify over `y`, the length of str created
    ex_X.mkInl.flip.iAlls'
