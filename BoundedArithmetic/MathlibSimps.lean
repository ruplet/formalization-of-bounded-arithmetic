-- In this file this is crucial to be careful with imports,
-- as all `simp` lemmas in scope will get our `delta0_simp` attribute!
import Lean
import Mathlib.Tactic.Simps.Basic

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity

import BoundedArithmetic.Register

open Lean Elab Command

elab "mkDelta0FromModelTheory" : command => do
  let env ← getEnv
  let targetMod : Name := `FirstOrder.Language
  -- Collect all decls with names under the target module *and* having `[simp]`
  for (declName, _) in env.constants do
    if targetMod.isPrefixOf declName then
      if (hasSimpAttribute env declName) then
        elabCommand (← `(attribute [delta0_simps] $(mkIdent declName)))

mkDelta0FromModelTheory
