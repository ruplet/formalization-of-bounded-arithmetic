import Lean

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.IsEnum
import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.LanguageZambella
import BoundedArithmetic.Syntax
import BoundedArithmetic.Semantics
import BoundedArithmetic.Order

open FirstOrder Language BoundedFormula Formula


-- i think that type level is set to 0 because of
-- Vars1x type is just Type
-- variable {α disp : Type}

-- Definition 3.4 (Induction Scheme), p. 35 od draft (46 of PDF)
-- Note that `phi(x)` is permitted to have free variables other than `x`
-- This means that ultimately we need to take universal closure of the
-- resulting Bounded Formula, to get a Sentence (no free vars)
-- expect 1 displayed free variable (`x`), thus DisplayedFV1
-- but we can have more free vars - we `forall` over them!
def mkInductionSentence
  {a} [IsEnum a] {name}
  {L : Language}
    [Zero $ L.Term Empty]
    [One $ L.Term (Vars1 name)]
    [Add $ L.Term (Vars1 name)]
  (phi: L.Formula ((Vars1 name) ⊕ a))
  : L.Sentence :=
  let univ := phi.iAlls'

  let base := univ.subst (fun _ => 0)

  let step_assumption := univ
  let step_target := univ.subst (fun _ => (var Vars1.fv1) + 1)
  let step' : L.Formula (Vars1 name) := step_assumption ⟹ step_target
  let step := step'.display1.flip.iAlls'

  let forall_x_holds := univ.display1.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds

syntax (name := simp_induction) "simp_induction" " at " (ppSpace ident)? : tactic

macro_rules
| `(tactic| simp_induction at $h:ident) =>
  `(tactic|
  conv at $h =>
    unfold Sentence.Realize mkInductionSentence
    rw [Formula.realize_imp];
    rw [Formula.realize_imp];

    conv =>
      lhs
      unfold Formula.Realize
      rw [BoundedFormula.realize_subst]
      change Formula.Realize _ _

    conv =>
      rhs; lhs
      rw [realize_iAlls'.Vars1]; ext
      rw [realize_flip]
      rw [realize_display1]
      rw [Formula.realize_imp];

      conv => lhs -- this is just `univ` already
      conv =>
        rhs
        unfold Formula.Realize
        rw [BoundedFormula.realize_subst]
        change Formula.Realize _ _
    simp only [delta0_simps]
    unfold Formula.Realize
    simp only [delta0_simps]
  )



def _root_.FirstOrder.Language.Formula.IsNum {n} (phi : zambella.Formula (Vars1 n)) :=
  let tp : zambella.Formula (Vars1 n) :=
    (Relations.boundedFormula₁
      ZambellaRel.isnum
      (var $ .inl .fv1)
    )
  tp ⟹ phi


-- open Lean Elab Tactic Meta
-- /-- Normalize the RHS of the induction sentence -/
-- syntax (name := normalizeIndRhs) "normalize_ind_rhs" (" at " ident)? : tactic

-- elab_rules : tactic
-- | `(tactic| normalize_ind_rhs at $h:ident) => do
--   evalTactic $ `(tactic|
--     -- normalize the `isOpen`, `isDelta0` etc. part
--     conv at $h =>
--       conv =>
--         lhs;
--         simp only [IsQF.relabelEquiv, IsOpen.display3, IsOpen.equal, IsQF.relabelEquiv.mp]
--       -- this has to work! the goal has to reduce to `True`.
--       rw [forall_const]

--       unfold Sentence.Realize mkInductionSentence
--       rw [Formula.realize_imp]
--       rw [Formula.realize_imp]
--       rhs; rhs;
--       unfold Formula.Realize
--       unfold iAlls' alls alls
--       rw [realize_all]; intro
--       rw [BoundedFormula.realize_relabel]
--       unfold Formula.flip
--       rw [BoundedFormula.realize_relabelEquiv]
--       unfold Formula.display1
--       -- here we unroll iAlls' over what `phi` came with!
--       rw [BoundedFormula.realize_relabelEquiv]
--       try unfold alls
--       try unfold alls
--       try unfold alls
--       try (rw [realize_all]; intro;)
--       try (rw [realize_all]; intro;)
--       try (rw [realize_all]; intro;)
--       rw [BoundedFormula.realize_relabel]
--       -- unfold alls
--       -- first | unfold display3 | unfold display2 | unfold display1
--       -- rw [BoundedFormula.realize_relabelEquiv]
--   )

def _root_.FirstOrder.Language.BoundedFormula.toFormula' {L : Language} {a} (phi : L.BoundedFormula a 0) : L.Formula a := phi

-- This is induction sentence creator which instead of ∀x, φ(x),
-- gives you ∀x : int, φ(x)
def mkInductionSentenceTyped
  {a} [IsEnum a] {name}
  {n}
  (phi: zambella.BoundedFormula ((Vars1 name) ⊕ a) n)
  : zambella.Sentence :=
  let univ := phi.alls.iAlls'

  let base := univ.subst (fun _ => 0)

  let step_assumption := univ
  let step_target : zambella.Formula (Vars1 name) := univ.subst (fun _ => (var .fv1) + 1)
  let step' : zambella.Formula (Vars1 name) := step_assumption ⟹ step_target
  let step := step'.IsNum.toFormula'.display1.flip.iAlls'

  let forall_x_holds := univ.IsNum.toFormula'.display1.flip.iAlls'
  base ⟹ step ⟹ forall_x_holds


-- Definition V.I.2 (Comprehension Axiom); p. 96 PDF; release of Logical Foundations
-- `X` cannot occur free in `phi(z)`, but `y` can
def mkComprehensionSentence {n} {a} [IsEnum a] {name}
  (phi: zambella.BoundedFormula (((Vars1 name) ⊕ (Vars1 .y)) ⊕ a) n)
  : zambella.Sentence :=
    -- now `y` is accessible and nothing else!
    let univ : zambella.Formula (Vars1 name ⊕ Vars1 FvName.y)
      := phi.alls.iAlls'

    -- X(z) ↔ φ(z)
    let iff : zambella.Formula (Vars3 .y .z .X) :=
      z ∈' X ⇔
      univ.subst (Sum.elim (fun _ => .var z.name) (fun _ => .var y.name))

    let iff : zambella.Formula (Vars1 .z ⊕ Vars2 .y .X) :=
      (display3 .z iff.rotate_213)

    let all_z : zambella.Formula (Vars2 .y .X) :=
      iBdAllLt' y iff.flip

    let X_type : zambella.Formula (Vars2 .y .X) :=
      Relations.boundedFormula₁ ZambellaRel.isstr X

    let X_def : zambella.Formula (Vars1 .X ⊕ Vars1 .y) :=
      (display2 .X (X_type ⊓ all_z).rotate_21)

    let ex_X : zambella.Formula _ := iBdEx' y X_def.flip

    -- quantify over `y`, the length of str created
    ex_X.mkInl.flip.iAlls'
