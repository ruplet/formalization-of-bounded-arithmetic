import Mathlib.ModelTheory.Semantics

open FirstOrder Language

variable {L : Language}
variable (M) [L.Structure M]
variable (r : L.Relations 2)
def reflexive : L.Sentence :=
  ∀' ∀' ∀' ((r.boundedFormula₂ &1 &0) ⊓ (r.boundedFormula₂ (&0) &4))
attribute [simp] BoundedFormula.alls BoundedFormula.exs Sentence.Realize Formula.Realize Formula.relabel Fin.snoc
theorem c : Sentence.Realize M (reflexive r) := by
  unfold reflexive
  simp
  -- now it's visible that deBruijn indices are in reverse order
  intro x y z
  sorry
