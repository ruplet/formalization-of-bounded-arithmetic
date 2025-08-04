import Lean
import Qq
open Lean Elab Tactic Term Meta Syntax PrettyPrinter Qq

namespace HilbertStyle

inductive Formula where
| var : Name -> Formula
| imp : Formula -> Formula -> Formula
deriving Repr, DecidableEq

notation:60 a " ==> " b => Formula.imp a b

def A1 (phi psi : Formula)
  := phi ==> psi ==> phi
def A2 (phi psi ksi : Formula)
  := (phi ==> psi ==> ksi) ==> (phi ==> psi) ==> phi ==> ksi

open Formula

-- perhaps we should be able to somehow take as axiom a formula,
-- for which the proof of being of the form A1 / A2 is non-constructive
-- i.e. have predicate isAxiom. but this is slightly harder in Lean
inductive Derivable : (List Formula) -> Formula -> Prop where
| assumption {Γ} {φ} : (φ ∈ Γ) -> Derivable Γ φ
| axK {Γ} {phi psi} : Derivable Γ $ A1 phi psi
| axS {Γ} {phi psi ksi} : Derivable Γ $ A2 phi psi ksi
| mp {Γ} {phi psi} : Derivable Γ (phi ==> psi) -> Derivable Γ phi -> Derivable Γ psi

declare_syntax_cat logic_expr

syntax ident : logic_expr
syntax logic_expr " -> " logic_expr : logic_expr
syntax "(" logic_expr ")" : logic_expr
syntax "[Logic| " logic_expr "]" : term

elab_rules : term
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

elab "hilbertDebug" : tactic => do
  let goal ← getMainTarget
  let ppGoal := goal.dbgToString
  logInfo m!"Goal expression: {ppGoal}"
  -- let goalType ← goal.getType
  let gamma ← extractGammaFromGoal

  logInfo m!"Gamma: {gamma}"

elab "by_mem" : tactic => do evalTactic (← `(tactic| simp [List.Mem]))

-- Syntax category for Hilbert proof steps
declare_syntax_cat hilbert_tactic
-- syntax "let " ident ":=" logic_expr : hilbert_tactic
syntax "have" ident ":" logic_expr "by" "assumption" : hilbert_tactic
syntax "have" ident ":=" "axK" logic_expr "," logic_expr : hilbert_tactic
syntax "have" ident ":=" "axS" logic_expr "," logic_expr "," logic_expr : hilbert_tactic
syntax "have" ident ":=" "mp" ident ident : hilbert_tactic
syntax "debug" : hilbert_tactic
syntax "exact " ident : hilbert_tactic

syntax "begin_hilbert " (hilbert_tactic)* : tactic

elab_rules : tactic
  | `(tactic| begin_hilbert $[$tacs:hilbert_tactic]*) => do
    for tacNode in tacs do
      let tac ← match tacNode with
        -- | `(hilbert_tactic| let $name:ident := $e:logic_expr) => do
        --     let e' <- `([Logic| $e])
        --     let phi' <- Lean.Elab.Term.elabTerm e' none
        --     let phi <- delab phi'
        --     `(tactic| let $name := $phi)
        | `(hilbert_tactic| debug) => do
            `(tactic| hilbertDebug)

        | `(hilbert_tactic| have $name:ident : $phi:logic_expr by assumption) => do
            -- let e1' <- `([Logic| $e1])
            -- withoutErrToSorry do
            let phi' ← Lean.Elab.Term.elabTerm phi none
            let phi <- delab phi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            let goal ← `(Derivable $gamma $phi)
            -- let goalTy := mkApp2 (mkConst ``Derivable) gamma' phi'
            -- let byMem ← `(by by_mem)
            -- let rhs ← mkAppM ``Derivable.assumption #[gamma', phi', ← Lean.Elab.Term.elabTerm byMem (some goalTy)]
            -- let goal <- getMainGoal
            -- let fVarId <- goal.assert name goalTy rhs

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
            let goal ← `(Derivable $gamma (A1 $phi $psi))
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
            `(tactic| have $name : Derivable $gamma (A2 $phi $psi $ksi) := Derivable.axS)

        | `(hilbert_tactic| have $name:ident := mp $h1 $h2) =>
            `(tactic| have $name := Derivable.mp $h1 $h2)

        | `(hilbert_tactic| exact $id:ident) =>
            `(tactic| exact $id)

        | _ => throwError m!"Unsupported tactic: {tacNode}"
      withTacticInfoContext tacNode do
        withMacroExpansion tacNode tac (evalTactic tac)
        -- evalTactic tac


def a : Name := `a
variable (φ ψ ϑ p q: Name)

def phi := [Logic| φ]
def pphi := [Logic| p -> q]

-- types of combinators A1 A2
def K_type (x y : Name) := [Logic| x -> y -> x]
def S_type (x y z : Name) := [Logic| (x -> y -> z) -> (x -> y) -> x -> z]


-- Urzyczyn, Sorensen: example 5.1.3
example {φ : Formula} : Derivable [] (φ ==> φ) := by
  have a : Derivable [] $ A2 φ (φ ==> φ) φ := Derivable.axS
  have b : Derivable [] $ A1 φ (φ ==> φ) := Derivable.axK
  have c := Derivable.mp a b
  have d : Derivable [] $ A1 φ φ := Derivable.axK
  exact Derivable.mp c d

example : Derivable [] [Logic| φ -> φ] := by
  begin_hilbert
    have a := axS φ, φ -> φ, φ
    have b := axK φ, φ -> φ
    have c := mp a b
    have d := axK φ, φ
    have e := mp c d
    exact e

-- Urzyczyn, Sorensen: example 5.1.4
example {φ ψ ϑ: Formula} : Derivable [φ, φ ==> ψ, ψ ==> ϑ] (ϑ) := by
  have a : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ φ ==> ψ := Derivable.assumption (by simp [List.Mem])
  have b : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ φ := Derivable.assumption (by simp [List.Mem])
  have c : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ ψ := Derivable.mp a b
  have d : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ ψ ==> ϑ := Derivable.assumption (by simp [List.Mem])
  have e : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ ϑ := Derivable.mp d c
  exact e

syntax "[Logic|" sepBy(logic_expr, ",") "⊢" logic_expr "]": term

elab_rules : term
  | `([Logic| $assumptions,* ⊢ $goal]) => do
    let assumpExprs ← assumptions.getElems.mapM (fun stx => elabTerm stx none)
    let goalExpr ← elabTerm goal none
    let listExpr <- Lean.Meta.mkListLit (mkConst ``Formula) assumpExprs.toList
    pure $ mkApp2 (mkConst ``Derivable) listExpr goalExpr

-- Urzyczyn, Sorensen: example 5.1.4
example : [Logic|φ, φ -> ψ, ψ -> ϑ ⊢  ϑ] := by
  begin_hilbert
    have a : φ -> ψ by assumption
    have b : φ by assumption
    have c := mp a b
    have d : ψ -> ϑ by assumption
    have e := mp d c
    exact e

end HilbertStyle
