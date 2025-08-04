import V0Theory.TwoSortedModelTheory.Basic
import V0Theory.TwoSortedModelTheory.Syntax

namespace L2

-- Step 1: Define the two sorts
inductive Sorts
| num : Sorts
| str : Sorts
deriving DecidableEq, Repr

inductive Functions00Num where
| zero
| one

inductive Functions00Str where
| eps

inductive Functions20Num where
| add
| mul

inductive Functions01Num where
| length

inductive Relations20
| eqnum
| leq

inductive Relations02
| eqstr

inductive Relations11
| ins

def Functions (arities: Sorts -> Nat) (retSort: Sorts) : Type
:= match retSort with
| Sorts.num =>
    match arities Sorts.num, arities Sorts.str with
    | 0, 0 => Functions00Num
    | 2, 0 => Functions20Num
    | 0, 1 => Functions01Num
    | _, _ => Empty
| Sorts.str =>
    match arities Sorts.num, arities Sorts.str with
    | 0, 0 => Functions00Str
    | _, _ => Empty

def Relations (arities: Sorts -> Nat) : Type
:= match arities Sorts.num, arities Sorts.str with
| 0, 2 => Relations02
| 2, 0 => Relations20
| 1, 1 => Relations11
| _, _ => Empty

def Lang : TwoSortedFirstOrder.Language Sorts :=
{ Functions := Functions,
  Relations := Relations
}

def varIndT := String
def TermTN n := TwoSortedFirstOrder.Language.Term Sorts Lang (varIndT ⊕ Fin n)
def TermT := TwoSortedFirstOrder.Language.Term Sorts Lang varIndT

inductive DeltaB0 : Nat -> Type
  -- here carefully: OpenFormula originally had argument {n}
| openFormula {n} {f : TwoSortedFirstOrder.Language.OpenFormula Sorts Lang varIndT} : DeltaB0 n
| boundedNumAll {n} (f : DeltaB0 (n + 1)) : DeltaB0 n
| boundedNumEx {n} (f : DeltaB0 (n + 1)) : DeltaB0 n

mutual
inductive SigmaB : Nat -> Nat -> Type
| exPi {nFree : Nat} {lv : Nat} (f : PiB (nFree + 1) lv) (t: TermT Sorts.num) : SigmaB nFree (lv + 1)
| exSigma {nFree : Nat} {lv : Nat} (f: SigmaB (nFree + 1) lv) (t: TermT Sorts.num): SigmaB nFree lv

inductive PiB : Nat -> Nat -> Type
| allSigma {nFree : Nat} {lv : Nat} (f : SigmaB (nFree + 1) lv) (t: TermT Sorts.num) : PiB nFree (lv + 1)
| allPi {nFree : Nat} {lv : Nat} (f: PiB (nFree + 1) lv) (t: TermT Sorts.num): PiB nFree lv
end


namespace FormulaBuilder
-- namespace TermBuilder

open TwoSortedFirstOrder.Language

def arities00 (_: Sorts) : Nat := 0
def arities20 (s: Sorts) : Nat :=
match s with
| Sorts.num => 2
| Sorts.str => 0


-- def nameSubset (name : varIndT) : varIndT ⊕ Fin 0 :=
--   Sum.inl name

def var (s: Sorts) (name: varIndT) : TermT s :=
  Term.var s name

-- /-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
-- @[simp]
-- def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
--   | _m, _n, _h, falsum => falsum
--   | _m, _n, h, equal t₁ t₂ =>
--     equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
--   | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
--   | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
--   | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all


def terms00 : (s: Sorts) -> (Fin (arities00 s)) -> (TermT s) := fun _ => Fin.elim0
-- def terms20 {a b : Nat} (t1: TermTN a Sorts.num) (t2: TermTN b Sorts.num) : (s: Sorts) -> (Fin (arities20 s)) -> TermTN (a + b) s :=
--   fun s =>
--   match s with
--   | Sorts.num =>
--     fun (i: Fin 2) =>
--     match i with
--     | 0 => t1.relabel Sorts Lang (varIndT ⊕ Fin a) (varIndT ⊕ Fin (a + b)) (Sum.map id (Fin.castLE (Nat.le_add_right a b)))
--     -- here, Fin.castLE is needed!
--     -- t1.relabel
--     | 1 => t2.relabel Sorts Lang (varIndT ⊕ Fin b) (varIndT ⊕ Fin (a + b)) (Sum.map id (Fin.castLE (Nat.le_add_left b a)))
--   | Sorts.str => Fin.elim0
def terms20 (t1 t2: TermT Sorts.num) : (s: Sorts) -> (Fin (arities20 s)) -> TermT s :=
  fun s =>
  match s with
  | Sorts.num =>
    fun (i: Fin 2) =>
    match i with
    | 0 => t1
    | 1 => t2
  | Sorts.str => Fin.elim0

def funZero : Lang.Functions arities00 Sorts.num := Functions00Num.zero
def funOne : Lang.Functions arities00 Sorts.num := Functions00Num.one
def funAdd : Lang.Functions arities20 Sorts.num := Functions20Num.add
def funMul : Lang.Functions arities20 Sorts.num := Functions20Num.mul

def zero : TermT Sorts.num :=
  Term.func Sorts.num funZero terms00

def one : TermT Sorts.num :=
  Term.func Sorts.num funOne terms00

def add (t1 t2 : TermT Sorts.num) : TermT Sorts.num :=
  Term.func Sorts.num funAdd (terms20 t1 t2)

def mul (t1 t2 : TermT Sorts.num) : TermT Sorts.num :=
  Term.func Sorts.num funMul (terms20 t1 t2)

-- end TermBuilder

-- open TwoSortedFirstOrder.Language

def OpenFormulaT := OpenFormula Sorts Lang varIndT

def relEqnum : Lang.Relations arities20 := Relations20.eqnum
def relLeqnum : Lang.Relations arities20 := Relations20.leq

def eqNum (t1 t2 : TermT Sorts.num) : OpenFormulaT :=
  OpenFormula.rel relEqnum (terms20 t1 t2)

def neNum (t1 t2 : TermT Sorts.num) : OpenFormulaT :=
  notf $ eqNum t1 t2

def leqNum (t1 t2 : TermT Sorts.num) : OpenFormulaT :=
  OpenFormula.rel relLeqnum (terms20 t1 t2)

def leNum (t1 t2 : TermT Sorts.num) : OpenFormulaT :=
  andf (leqNum t1 t2) (neNum t1 t2)

def imp (p q : OpenFormulaT) : OpenFormulaT :=
  OpenFormula.imp p q

notation:100 "%" x => (var Sorts.num x)
notation:50 t1 " + " t2 => add t1 t2
notation:50 t1 " * " t2 => mul t1 t2
notation:45 t1 " <n " t2 => leNum t1 t2
notation:45 t1 " <=n " t2 => leqNum t1 t2
notation:40 t1 " =n " t2 => eqNum t1 t2
notation:40 t1 " !=n " t2 => neNum t1 t2
notation:30 phi " & " psi => andf phi psi
notation:30 phi " ==> " psi => imp phi psi
notation:20 "!" phi => notf $ phi

variable (x y : varIndT)

-- the type of this should be Sentence L2
def B1 : OpenFormulaT :=
  ((%x) + one) !=n zero

def B2 : OpenFormulaT :=
  (((%x) + one) =n ((%y) + one)) ==> ((%x) =n (%y))

def B3 : OpenFormulaT :=
  ((%x) + zero) =n (%x)

def B4 : OpenFormulaT :=
  ((%x) + ((%y) + one)) =n (((%x) + (%y)) + one)

def B5 : OpenFormulaT :=
  ((%x) * zero) =n zero

def B6 : OpenFormulaT :=
  ((%x) * ((%y) + one)) =n (((%x) * (%y)) + (%x))

def B7 : OpenFormulaT :=
  (((%x) <=n (%y)) & ((%y) <=n (%x))) ==> ((%x) =n (%y))

def B8 : OpenFormulaT :=
  (%x) <=n ((%x) + (%y))

def B9 : OpenFormulaT :=
  (%x) <=n zero

def C : OpenFormulaT :=
  (zero + one) =n one

-- here, define Comprehension, Number Induction, Min, Max
abbrev TheoryL2 := Multiset OpenFormulaT

-- The type of this should be Theory L2
def TwoBasic : TheoryL2  :=
[
  Formula.all (B1 x),
  -- B2,
  -- B3,
  -- B4,
  -- B5,
  -- B6,
  B7 x y,
  -- B8,
  B9 x,
  -- B10,
  -- B11,
  -- B12,
  -- L1,
  -- L2,
  -- SE
]


-- (* Exercise 5.1.a: not x < 0 *)
-- lemma exercise_5_1_a: "~ (x < 0)"
-- proof
--   assume "x < 0"
--   then have "x <= 0" and "x ~= 0" by simp_all
--   from B9 have "0 <= x" .
--   then have "((x <= 0) \<and> (0 <= x)) --> (x = 0)" using B7 by blast
--   then have "x = 0" using `x <= 0` `0 <= x` by blast
--   with `x ~= 0` show False by contradiction
-- qed

def e1 := ((%x) <n zero)

def exercise51aStmt : OpenFormulaT :=
  !((%x) <n zero)

-- theorem exercise51a {x y} : provable Sorts Lang varIndT (TwoBasic x y) (exercise51aStmt x) :=
--   by
--     constructor
--     unfold exercise51aStmt
--     unfold notf
--     apply prf.impI
--     unfold leNum
--     simp
--     unfold TwoBasic
--     sorry
    -- have h : axm1 Sorts Lang varIndT (TwoBasic x y) ((var Sorts.num x <=n zero) & (var Sorts.num x !=n zero))


-- now, corollary V.1.7: V0 proves X-IND

-- def Comprehension :
end FormulaBuilder


-- How to define special tactic language for easier proving in object logic?
-- concept: https://lean-forward.github.io/lean-together/2019/slides/hudon.pdf
-- shitty: https://github.com/unitb/temporal-logic/blob/amsterdam-talk/src/temporal_logic/tactic.lean
-- real?: https://github.com/leanprover-community/iris-lean/blob/master/src/Iris/ProofMode/Display.lean

-- def M (s: Sorts) : Type :=
-- match s with
-- | Sorts.num => Nat
-- | Sorts.str => Finset Nat

-- -- def standardFuns {sort : Sorts} {arities : Sorts -> Nat} (f : Lang.Functions arities sort) : ((s : Sorts) → Fin (arities s) → M s) -> M sort :=
-- --   fun realizer =>
-- --     match f with
-- --     |

-- def StandardModel : TwoSortedFirstOrder.Language.Structure Sorts Lang M where
--   funMap := fun s arities f args =>
--     match s, arities, f with
--     | Sorts.num, _, funZero => (0: Nat)
--     | Sorts.num, _, funOne => (1: Nat)
--     | Sorts.num, _, funAdd =>
--       let x := args Sorts.num (0 : Fin 2)
--       let y := args Sorts.num 1
--       x + y


end L2
