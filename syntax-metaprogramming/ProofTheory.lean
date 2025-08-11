import Lean

namespace MinimalLogic

open Lean Elab Tactic Term Meta Syntax

/-
  Step 1: Define custom syntax for minimal logic
-/

declare_syntax_cat logic_expr

syntax "⊤"                        : logic_expr
syntax "⊥"                        : logic_expr
syntax logic_expr " ∧ " logic_expr : logic_expr
syntax logic_expr " ∨ " logic_expr : logic_expr
syntax logic_expr " → " logic_expr : logic_expr
syntax ident                      : logic_expr
syntax "(" logic_expr ")" : logic_expr

syntax "[Logic| " logic_expr "]" : term

/-
  Step 2: Macro expansion to Lean's internal logic
-/

elab_rules : term
  | `([Logic| ⊤]) => return mkConst ``True
  | `([Logic| ⊥]) => return mkConst ``False
  | `([Logic| ($p)]) => do elabTerm (← `([Logic| $p])) none -- Recurse for parentheses
  | `([Logic| $p:logic_expr ∧ $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkAppM ``And #[lhs, rhs]
  | `([Logic| $p:logic_expr ∨ $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkAppM ``Or #[lhs, rhs]
  | `([Logic| $p:logic_expr → $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkArrow lhs rhs
  | `([Logic| $i:ident]) =>
      elabTerm (mkIdent i.getId) none

declare_syntax_cat minitactic
syntax "assume " ident " : " term                       : minitactic
syntax "introa " ident                                  : minitactic
syntax "introduce " term                                : minitactic
syntax "apply " ident                                   : minitactic
syntax "exact " ident                                   : minitactic
syntax "split"                                          : minitactic
syntax "left"                                           : minitactic
syntax "right"                                          : minitactic
syntax "cases " ident                                   : minitactic
syntax "done"                                           : minitactic

syntax "begin_min " (minitactic)*  : tactic


elab_rules : tactic
  | `(tactic| begin_min $[$tacs:minitactic]*) => do
      -- let mut tacList : Array (TSyntax `tactic) := #[]
      for tacNode in tacs do
        let newTac : TSyntax `tactic ← match tacNode with
          | `(minitactic| assume $h:ident : $ty) => `(tactic| have $h : $ty := sorry)
          | `(minitactic| introa $h:ident)       => `(tactic| intro a)
          | `(minitactic| introduce $h:term)       => `(tactic| intro $h:term)
          | `(minitactic| apply $h:ident)       => `(tactic| apply $h)
          | `(minitactic| exact $h:ident)       => `(tactic| exact $h)
          | `(minitactic| split)                => `(tactic| constructor)
          | `(minitactic| left)                 => `(tactic| apply Or.inl)
          | `(minitactic| right)                => `(tactic| apply Or.inr)
          | `(minitactic| done)                 => `(tactic| assumption)
          | _ => throwError m!"Unsupported mini tactic: {tacNode}"
        -- tacList := tacList.push newTac
        withTacticInfoContext tacNode do
          evalTactic newTac

example (P Q : Prop) : [Logic| P → (Q → P)] := by
  begin_min
    introduce p
    introduce q
    done

def I' {a : Type} := a -> a
def I {a : Type} : @I' a := fun x => x

def C' {a b c : Type} := (a -> b -> c) -> b -> a -> c
def C {a b c : Type} : @C' a b c := fun f g x => f x g

def K' {a b : Type} := a -> b -> a
def K {a b : Type} : @K' a b := fun x _ => x

def S' {a b c : Type} := (a -> b -> c) -> (a -> b) -> a -> c
def S {a b c : Type} : @S' a b c := fun x y z => x z (y z)

def B'{a b c : Type} := (b -> c) -> ((a -> b) -> (a -> c))
def B {a b c : Type} : @B' a b c := S (K S) K

#reduce B
#check S (K S) K
#check B
set_option pp.mvars true
set_option pp.all true
#check C K K
#check @C _ _ _ K K
#check @B Nat Bool String

-- w sumie tutaj widać że typ to identyczność!
#check ((S K) K)
#check ((C K) K)
#check (C K K)

#check (B C C (C B K S) S S)

elab "inferPretty " t:term : term => do
  let e ← Term.elabTerm t none
  let ty ← inferType e
  forallTelescopeReducing ty fun args body => do
    let pretty ← mkForallFVars args body
    logInfo m!"Inferred type:\n{← ppExpr pretty}"
    return mkConst ``True

#eval inferPretty (B C K)


-- def B' := S' (K' S') K'
-- def B {a b c : Type} := fun f g x => f (g x)

-- SKK = I


def i {a : Type} : @I' a := by
  unfold I'
  intro
  assumption



end MinimalLogic
