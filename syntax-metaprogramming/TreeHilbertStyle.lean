--== SKIP BELOW FOR DEMONSTRATION ====================================
import Lean
import Qq
open Lean Elab Tactic Term Meta Syntax PrettyPrinter Qq

-- Section 1:
-- + Deep embedding of Hilbert-style proof calculus
-- + Custom syntactic macros and elaboration rules for
--   ease of use of the object theory
-- + Tactics to enable reasoning inside of Hilbert without
--   having to apply List theorems / rewrite, simp etc.
namespace HilbertStyle

inductive Formula where
| var : Name -> Formula
| imp : Formula -> Formula -> Formula
deriving Repr, DecidableEq
open Formula

notation:60 a " ==> " b => imp a b

def K (φ ψ : Formula) := φ ==> ψ ==> φ
def S (φ ψ ξ : Formula) := (φ ==> ψ ==> ξ) ==> (φ ==> ψ) ==> φ ==> ξ

-- perhaps we should be able to somehow take as axiom an arbitrary formula,
-- i.e. enable Lean-reasoning of "if ax is an axiom" -> "Γ ⊢ ax"
-- now we don't provide a decidable procedure for "given φ : Formula, is φ an axiom?"
-- nor we plan to...
inductive Derivable : (List Formula) -> Formula -> Prop where
| assumption {Γ} {φ} : (φ ∈ Γ) -> Derivable Γ φ
| axK {Γ} {phi psi} : Derivable Γ $ K phi psi
| axS {Γ} {phi psi ksi} : Derivable Γ $ S phi psi ksi
| mult_mp {Γ1 Γ2} {phi psi} : Derivable Γ2 (phi ==> psi) -> Derivable Γ1 phi -> Derivable (Γ1 ++ Γ2) psi

declare_syntax_cat logic_expr

scoped syntax ident : logic_expr
scoped syntax logic_expr " -> " logic_expr : logic_expr
scoped syntax "(" logic_expr ")" : logic_expr
scoped syntax "[Logic| " logic_expr "]" : term

scoped elab_rules : term
  | `([Logic| $e:logic_expr]) => elabTerm e none
  | `(logic_expr| $i:ident) => do
      let nameExpr ← Term.elabTerm i none
      return mkApp (mkConst ``Formula.var) nameExpr

  | `(logic_expr| $p:logic_expr -> $q:logic_expr) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.imp) lhs rhs

  | `(logic_expr| ($p)) => do
      elabTerm (← `([Logic| $p])) none

partial def extractGammaFromGoal : TacticM Expr := do
  let goal ← getMainTarget
  let goal <- whnf goal
  match goal with
  | Expr.app (Expr.app (Expr.const name _) gamma) _ =>
    if name == `HilbertStyle.Derivable then
      pure gamma
    else
      throwError "Goal head constant is not HilbertStyle.Derivable, got: {name}"
  | _ =>
    throwError "Goal is not of the form `HilbertStyle.Derivable Γ φ`, got: {goal}"

scoped elab "hilbertDebug" : tactic => do
  let goal ← getMainTarget
  let ppGoal := goal.dbgToString
  logInfo m!"Goal expression: {ppGoal}"
  -- let goalType ← goal.getType
  let gamma ← extractGammaFromGoal

  logInfo m!"Gamma: {gamma}"

scoped elab "by_mem" : tactic => do evalTactic (← `(tactic| simp [List.Mem]))

-- Syntax category for Hilbert proof steps
declare_syntax_cat hilbert_tactic
scoped syntax "have" ident ":" logic_expr "by" "assumption" : hilbert_tactic
scoped syntax "have" ident ":=" "axK" logic_expr "," logic_expr : hilbert_tactic
scoped syntax "have" ident ":=" "axS" logic_expr "," logic_expr "," logic_expr : hilbert_tactic
scoped syntax "have" ident ":=" "mult_mp" ident ident : hilbert_tactic
scoped syntax "debug" : hilbert_tactic
scoped syntax "exact " ident : hilbert_tactic

scoped syntax "begin_hilbert " (hilbert_tactic)* : tactic

scoped elab_rules : tactic
  | `(tactic| begin_hilbert $[$tacs:hilbert_tactic]*) => do
    for tacNode in tacs do
      let tac ← match tacNode with
        | `(hilbert_tactic| debug) => do
            `(tactic| hilbertDebug)

        | `(hilbert_tactic| have $name:ident : $phi:logic_expr by assumption) => do
            let phi' ← Lean.Elab.Term.elabTerm phi none
            let phi <- delab phi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            let goal ← `(Derivable $gamma $phi)
            `(tactic| have $name : $goal := @Derivable.assumption _ $phi (by by_mem))

        | `(hilbert_tactic| have $name:ident := axK $e1, $e2) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let phi <- delab phi'
            let psi <- delab psi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            let goal ← `(Derivable $gamma (K $phi $psi))
            `(tactic| have $name : $goal := Derivable.axK)

        | `(hilbert_tactic| have $name:ident := axS $e1, $e2, $e3) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let e3' <- `([Logic| $e3])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let ksi' ← Lean.Elab.Term.elabTerm e3' none
            let phi <- delab phi'
            let psi <- delab psi'
            let ksi <- delab ksi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            `(tactic| have $name : Derivable $gamma (S $phi $psi $ksi) := Derivable.axS)

        | `(hilbert_tactic| have $name:ident := mult_mp $h1 $h2) =>
            `(tactic| have $name := Derivable.mult_mp $h1 $h2)

        | `(hilbert_tactic| exact $id:ident) =>
            `(tactic| exact $id)

        | _ => throwError m!"Unsupported tactic: {tacNode}"
      withTacticInfoContext tacNode do
        -- withMacroExpansion tacNode tac (evalTactic tac)
        evalTactic tac

scoped syntax "[Logic|" sepBy(logic_expr, ",") "⊢" logic_expr "]": term

scoped elab_rules : term
  | `([Logic| $assumptions,* ⊢ $goal]) => do
    let assumpExprs ← assumptions.getElems.mapM (fun stx => elabTerm stx none)
    let goalExpr ← elabTerm goal none
    let listExpr <- Lean.Meta.mkListLit (mkConst ``Formula) assumpExprs.toList
    pure $ mkApp2 (mkConst ``Derivable) listExpr goalExpr

end HilbertStyle


-- Section 2: =========================================================
-- + Demo

variable (φ ψ ϑ p q: Name)

-- Urzyczyn, Sorensen: example 5.1.3
namespace HilbertStyle
-- version 1: no embedding used
example {φ : Formula} : Derivable [] (φ ==> φ) := by
  have a : Derivable [] $ S φ (φ ==> φ) φ := Derivable.axS
  have b : Derivable [] $ K φ (φ ==> φ) := Derivable.axK
  have c := Derivable.mult_mp a b
  have d : Derivable [] $ K φ φ := Derivable.axK
  exact Derivable.mult_mp c d

-- version 2: inside embedding!
example : Derivable [] [Logic| φ -> φ] := by
  begin_hilbert
    have a := axS φ, φ -> φ, φ
    have b := axK φ, φ -> φ
    have c := mult_mp a b
    have d := axK φ, φ
    have e := mult_mp c d
    exact e

-- strengthen to arbitrary Γ, will be needed in proof of deduction
-- syntax for variables meaning sets of formulas not yet supported!
theorem urzyczyn5_1_3' {φ : Formula} {Γ} : Derivable Γ (φ ==> φ) := by
  have a : Derivable Γ $ S φ (φ ==> φ) φ := Derivable.axS
  have b : Derivable [] $ K φ (φ ==> φ) := Derivable.axK
  have c := Derivable.mult_mp a b
  have d : Derivable [] $ K φ φ := Derivable.axK
  exact Derivable.mult_mp c d

-- Urzyczyn, Sorensen: example 5.1.6, version 1 (no embedding)
example {φ ψ ϑ: Formula} : Derivable [φ, φ ==> ψ, ψ ==> ϑ] (ϑ) := by
  have a : Derivable [φ ==> ψ] $ φ ==> ψ := Derivable.assumption (by simp [List.Mem])
  have b : Derivable [φ] $ φ := Derivable.assumption (by simp [List.Mem])
  have c : Derivable [φ, φ ==> ψ] $ ψ := Derivable.mult_mp a b
  have d : Derivable [ψ ==> ϑ] $ ψ ==> ϑ := Derivable.assumption (by simp [List.Mem])
  have e : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ ϑ := Derivable.mult_mp d c
  exact e

-- version 2
-- Urzyczyn, Sorensen: example 5.1.6, version 2
-- sorry! for multiplicative mp, we need syntax to declare how
-- the assumption set Γ is distributed to proof of premises
-- it's not there yet!
-- example : [Logic| φ, φ -> ψ, ψ -> ϑ ⊢ ϑ] := by
  -- begin_hilbert
    -- have a : φ -> ψ by assumption
    -- have b : φ by assumption
    -- have c := mult_mp a b
    -- have d : ψ -> ϑ by assumption
    -- have e := mult_mp d c
    -- exact e

end HilbertStyle


-- Section 3: =========================================================
-- + proofs in meta-theory about implementation of the proof calculus
--   weakening and deduction theorems
theorem weakening {Γ} {φ ψ} : HilbertStyle.Derivable Γ ψ -> HilbertStyle.Derivable (φ :: Γ) ψ := by
  intro h
  induction h with
  | assumption mem =>
    apply HilbertStyle.Derivable.assumption
    rw [List.mem_cons]
    right
    exact mem
  | axK => apply HilbertStyle.Derivable.axK
  | axS => apply HilbertStyle.Derivable.axS
  | mult_mp imp base imp_ih base_ih =>
    apply HilbertStyle.Derivable.mult_mp imp base_ih

-- Urzyczyn, Sorensen: proposition 5.1.7
-- this proof is conducted in the meta theory!
theorem deduction {Γ} {φ ψ}: HilbertStyle.Derivable (φ :: Γ) ψ <-> HilbertStyle.Derivable Γ (HilbertStyle.Formula.imp φ ψ) := by
  apply Iff.intro
  {
    -- trick to bypass "index in target's type is not a variable" at `induction h`
    intro h
    generalize hΓ' : φ :: Γ = Γ' at h
    induction h generalizing φ Γ with
    | @assumption _ h1 mem =>
      cases mem with
      | head =>
        injection hΓ' with head_eq
        rw [head_eq]
        apply HilbertStyle.urzyczyn5_1_3'
      | tail _ mem =>
        injection hΓ' with _ tail_eq
        rw [<- tail_eq] at mem
        have aux : HilbertStyle.Derivable Γ h1 := by
          apply HilbertStyle.Derivable.assumption
          assumption
        have aux2 : HilbertStyle.Derivable [] (h1 ==> φ ==> h1) := by
          apply HilbertStyle.Derivable.axK
        rw [<- List.append_nil Γ]
        apply HilbertStyle.Derivable.mult_mp aux2 aux
    | @axK _ phi psi =>
      have aux : HilbertStyle.Derivable Γ (HilbertStyle.K phi psi) := by
        apply HilbertStyle.Derivable.axK
      have aux2 : HilbertStyle.Derivable [] ((HilbertStyle.K phi psi) ==> φ ==> (HilbertStyle.K phi psi)) := by
        apply HilbertStyle.Derivable.axK
      rw [<- List.append_nil Γ]
      apply HilbertStyle.Derivable.mult_mp aux2 aux
    | @axS _ phi psi ksi =>
      have aux : HilbertStyle.Derivable Γ (HilbertStyle.S phi psi ksi) := by
        apply HilbertStyle.Derivable.axS
      have aux2 : HilbertStyle.Derivable [] ((HilbertStyle.S phi psi ksi) ==> φ ==> (HilbertStyle.S phi psi ksi)) := by
        apply HilbertStyle.Derivable.axK
      rw [<- List.append_nil Γ]
      apply HilbertStyle.Derivable.mult_mp aux2 aux
    | @mult_mp Γ1 Γ2 φ' ψ' imp base imp_ih base_ih =>
      rw [List.cons_eq_append_iff] at hΓ'
      have aux : HilbertStyle.Derivable [] (HilbertStyle.S φ φ' ψ') := by
        apply HilbertStyle.Derivable.axS
      obtain ⟨rfl, rfl⟩ | ⟨Γ2', rfl, rfl⟩ := hΓ'
      · have aux2 := HilbertStyle.Derivable.mult_mp aux (imp_ih rfl)
        -- we don't need to use base_ih here (which is impossible to instantiate)
        -- because we can derive φ -> φ' just from φ', which is `base`!!
        have aux3 : HilbertStyle.Derivable [] (φ' ==> φ ==> φ') := by
          apply HilbertStyle.Derivable.axK
        have aux4 := HilbertStyle.Derivable.mult_mp aux3 base
        have aux3 := HilbertStyle.Derivable.mult_mp aux2 aux4
        rwa [List.nil_append, List.append_nil] at aux3
      · have aux2 := base_ih rfl
        have aux3 : HilbertStyle.Derivable [] (HilbertStyle.K (φ' ==> ψ') φ) := by
          apply HilbertStyle.Derivable.axK
        have aux4 := HilbertStyle.Derivable.mult_mp aux3 imp
        have aux_S : HilbertStyle.Derivable [] (HilbertStyle.S φ φ' ψ') := by
          apply HilbertStyle.Derivable.axS

        have aux6 := HilbertStyle.Derivable.mult_mp aux_S aux4
        have aux7 := HilbertStyle.Derivable.mult_mp aux6 aux2
        repeat rw [List.append_nil] at aux7
        exact aux7
  }
  {
    -- this is slightly different to the proof in the book
    -- we don't use weakening in this version due to multiplicative mp
    intro h
    have aux_base : HilbertStyle.Derivable [φ] φ := by
      apply HilbertStyle.Derivable.assumption
      simp
    apply HilbertStyle.Derivable.mult_mp h aux_base
  }
