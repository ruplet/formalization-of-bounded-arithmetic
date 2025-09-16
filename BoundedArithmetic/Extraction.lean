import Lean.Meta.Constructions.RecOn
import Lean.Meta.Reduce
import Lean.Meta.Basic
import Lean.Meta.Eval
import Lean.Meta.Tactic

universe u
variable {num str: Type u}
variable [Zero num] [One num] [Add num] [Mul num] [LE num] [Membership num str]

-- this necessary for proof by split on |X| = 0 / |X| ≠ 0
variable (hDecEqNum : DecidableEq num)

class HasLen (str : Type u) (num : Type u) where
  len : str -> num
variable [HasLen str num]

-- we add seq and numones as special symbols for fast prototyping,
-- although they are definable in V^0
variable (seq : num -> str -> num) (numones : num -> str -> num)

def pair (x y : num) := (x + y) * (x + y + 1) + (1 + 1) * y

notation "⟨" i "," j "⟩" => pair i j
local notation "|" Z "|" => HasLen.len Z
local notation Z"["w"]" => seq w Z

instance : LT num where
  lt a b := a <= b ∧ a ≠ b

structure V0 where
  b1  : ∀ x : num, x + (1 : num) ≠ 0
  b2  : ∀ x y : num, x + 1 = y + 1 → x = y
  b3  : ∀ x : num, x + 0 = x
  b4  : ∀ x y : num, x + (y + 1) = (x + y) + 1
  b5  : ∀ x : num, x * 0 = 0
  b6  : ∀ x y : num, x * (y + 1) = (x * y) + x
  b7  : ∀ x y : num, x ≤ y -> y ≤ x → x = y
  b8  : ∀ x y : num, x ≤ x + y
  b9  : ∀ x : num, 0 ≤ x
  b10 : ∀ x y : num, x ≤ y ∨ y ≤ x
  b11 : ∀ {x y : num}, x ≤ y ↔ x < y + 1
  b12 : ∀ x : num, x ≠ 0 → ∃ y : num, y ≤ x ∧ y + 1 = x

  c   : (0 : num) + 1 = 1

  l1  : ∀ {X : str} {y : num}, y ∈ X → y < |X|
  l2  : ∀ {X : str} {y : num}, y + 1 = |X| → y ∈ X
  se  : ∀ (X Y : str),
          ((|X| = HasLen.len (num := num) Y ) ∧ ∀ (i : num), i < |X| → (i ∈ X ↔ i ∈ Y)) → X = Y

/-- Boolean XOR on `Prop`. -/
@[inline] def pxor (p q : Prop) : Prop := (p ∧ ¬ q) ∨ (¬ p ∧ q)
infixl:55 " ⊕ " => pxor

/-- 3-ary XOR (associative fold). -/
@[inline] def xor3 (p q r : Prop) : Prop := (p ⊕ q) ⊕ r

/-- Majority of three booleans (true iff at least two are true). -/
@[inline] def MAJ (p q r : Prop) : Prop :=
  (p ∧ q) ∨ (p ∧ r) ∨ (q ∧ r)

/-- Carry(i, X, Y) as in the book (V.4.17): existence of a “last joint 1”
    before `i` and no higher joint zeros thereafter up to `i`.  This matches (55). -/
def Carry (i : num) (X Y : str) : Prop :=
  ∃ k : num,
    k < i ∧ k ∈ X ∧ k ∈ Y ∧
    ∀ j : num, j < i → (k < j → (j ∈ X ∨ j ∈ Y))

def Empty_ax (Y : str) : Prop := ∀ i : num, i ∈ Y ↔
  i < 0

def Succ_ax (X Y : str) : Prop := ∀ i, i ∈ Y ↔
  i ≤ |X| ∧ (
    (i ∈ X ∧ ∃ j : num, j < i ∧ ¬ (j ∈ X))
    ∨ (¬ (i ∈ X) ∧ ∀ j : num, j < i → j ∈ X)
  )

def Add_ax (X Y Z : str) : Prop := ∀ i, i ∈ Z ↔
  i < |X| + |Y| ∧ xor3 (i ∈ X) (i ∈ Y) (Carry i X Y)

-- this is in mathlib
def ExistsUnique (p : num → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x
syntax "∃!" ident ", " term : term
macro_rules
  | `(∃! $x:ident, $p) =>
      `(ExistsUnique (fun $x => $p))

theorem not_x_lt_zero {x : num} :
  ¬ x < 0 :=
by
  sorry

theorem pred_exists {x : num} :
  x ≠ 0 → ∃ y, y ≤ x ∧ x = y + 1 :=
by
  sorry

-- comprehension instance needed for the theorem below
def comprehension1 :=
  -- this is an open formula
  let phi (z : num) := z < (0 : num)
  ∀ y, ∃ X : str, |X| <= y ∧ ∀ z, z < y -> (z ∈ X ↔ phi z)
theorem Empty_total_unique (hV0 : V0 (num := num) (str := str)) (hComp : comprehension1 (num := num) (str := str))
  : ∃! Y, Empty_ax (num := num) (str := str) Y :=
by
  obtain ⟨empty, hempty⟩ := hComp 0

  obtain ⟨h_len_empty_le_zero, h_empty_ax⟩ := hempty
  have h_len_empty_eq_zero := V0.b7 hV0 |empty| 0 h_len_empty_le_zero (V0.b9 hV0 |empty|)

  exists empty
  constructor
  · simp only [Empty_ax]
    intro i
    constructor
    · intro h_i_in_empty
      have h_i_lt_len_empty :=  V0.l1 hV0 h_i_in_empty
      rw [h_len_empty_eq_zero] at h_i_lt_len_empty
      exact h_i_lt_len_empty
    · intro h_i_lt_zero
      exact (h_empty_ax i h_i_lt_zero).mpr (by simp only; assumption)
  · intro Y hY
    apply V0.se hV0
    constructor
    · rw [h_len_empty_eq_zero]
      false_or_by_contra
      rename_i h_Y_nonempty
      obtain ⟨witness_Y, ⟨_, h_pred_len_Y_eq⟩⟩ := pred_exists h_Y_nonempty
      have h_witness_Y := V0.l2 hV0 h_pred_len_Y_eq.symm
      unfold Empty_ax at hY
      have witness_Y_lt_zero := (hY witness_Y).mp h_witness_Y
      exact not_x_lt_zero witness_Y_lt_zero
    · intro i _ -- h_i_lt_len_Y
      constructor
      · intro h_i_in_Y
        have i_lt_zero := (hY i).mp h_i_in_Y
        exfalso
        exact not_x_lt_zero i_lt_zero
      · intro h_i_in_empty
        have i_lt_zero := V0.l1 hV0 h_i_in_empty
        rw [h_len_empty_eq_zero] at i_lt_zero
        exfalso
        exact not_x_lt_zero i_lt_zero

theorem not_lt_zero {x : num} :
  ¬ x < 0 :=
by
  sorry

theorem le_refl {x : num} :
  x <= x :=
by
  sorry

theorem not_lt_refl {x : num} :
  ¬ (x < x) :=
by
  sorry

theorem le_trans {x y z : num} :
  x <= y -> y <= z -> x <= z :=
by
  sorry

theorem lt_trans {x y z : num} :
  x < y -> y < z -> x < z :=
by
  sorry

theorem lt_le_trans {x y z : num} :
  x < y -> y <= z -> x < z :=
by
  sorry

theorem le_lt_trans {x y z : num} :
  x <= y -> y < z -> x < z :=
by
  sorry

theorem le_weaken {x y z : num} :
  x <= y -> x <= y + z :=
by
  sorry

theorem lt_weaken {x y z : num} :
  x < y -> x < y + z :=
by
  sorry

theorem neq_split {x y : num} :
  x ≠ y -> (x > y ∨ x < y) :=
by
  sorry

theorem add_le_cancel {x y z : num} :
  x <= y -> x + z <= y + z :=
by
  sorry

theorem add_lt_cancel {x y z : num} :
  x < y -> x + z < y + z :=
by
  sorry


-- def Comprehension {m n}
--   (phi : (Fin m -> num) -> (Fin n -> str) -> Prop)
--   (nums : Fin m -> num)
--   (strs : Fin n -> str) :=
--   ∀ y, ∃ X : str, |X| <= y ∧ ∀ z, z < y -> (z ∈ X ↔ phi nums strs)


-- code(Succ_total_unique) := fun (X : str) (hComp : comp2 ..) -> hComp (|X| + 1)

def comprehension2 (OrigStr : str) :=
  -- sigma0B formula!
  let phi (X : str) (i : num) :=
    (i ∈ X ∧ ∃ j : num, j < i ∧ ¬ j ∈ X)
    ∨ (¬ i ∈ X ∧ ∀ j : num, j < i → j ∈ X)
  ∀ y, ∃ X : str, |X| <= y ∧ ∀ z, z < y -> (z ∈ X ↔ phi OrigStr z)
theorem Succ_total_unique (hV0 : V0 (num := num) (str := str)) (hDecEqNum := hDecEqNum)
  {X : str}
  (hComp : comprehension2 (num := num) (str := str) X)
  : ∃! Y, Succ_ax (num := num) (str := str) X Y :=
by
  obtain ⟨Y, hY⟩ := hComp (|X| + 1)
  exists Y
  constructor
  -- Prove that Succ(X) exists
  · simp only [Succ_ax]
    intro i
    constructor
    · intro h_i_in_Y
      constructor
      · have i_lt_len_Y := V0.l1 hV0 h_i_in_Y
        rw [V0.b11 hV0]
        apply lt_le_trans i_lt_len_Y hY.left
      · by_cases h_i_in_X : i ∈ X
        · left
          constructor
          · assumption
          · have aux :=
              ((hY.right i (by
              apply lt_weaken
              exact V0.l1 hV0 h_i_in_X
            )).mp h_i_in_Y)
            simp only at aux
            cases aux with
            | inl hl => exact hl.right
            | inr hr => exfalso; apply hr.left; exact h_i_in_X
        · right
          constructor
          · assumption
          · intro j hj
            have aux :=
              ((hY.right i (by
                have h_i_lt_len_Y := V0.l1 hV0 h_i_in_Y
                exact lt_le_trans h_i_lt_len_Y hY.left
              )).mp h_i_in_Y)
            simp only at aux
            cases aux with
            | inl hl => exfalso; apply h_i_in_X; exact hl.left
            | inr hr => apply hr.right; exact hj
    · intro hi
      have aux :=
        (hY.right i (by
        exact (V0.b11 hV0).mp hi.left
      )).mpr
      simp only at aux
      apply aux
      clear aux
      cases hi.right with
      | inl hi_l => left; assumption
      | inr hi_r => right; assumption
  -- Prove that Succ(X) is unique
  · intro Y2 hY2
    simp only at hY
    simp only [Succ_ax] at hY2
    have eq_ext : ∀ i, i ∈ Y ↔ i ∈ Y2 := by
      intro i
      constructor
      · intro hi
        have aux :=
          (hY.right i (by
            have h_i_lt_len_Y := V0.l1 hV0 hi
            exact lt_le_trans h_i_lt_len_Y hY.left
          )).mp hi
        specialize hY2 i
        apply hY2.mpr
        constructor
        · cases aux with
          | inl aux_l =>
            rw [V0.b11 hV0]
            apply lt_weaken
            exact V0.l1 hV0 aux_l.left
          | inr aux_r =>
            have i_lt_len_Y := V0.l1 hV0 hi
            have i_lt := lt_le_trans i_lt_len_Y hY.left
            rw [V0.b11 hV0]
            exact i_lt
        · exact aux
      · intro hi
        specialize hY2 i
        have hY2' := (hY2.mp hi).right
        have aux :=
          (hY.right i (by
          rw [<- V0.b11 hV0]
          exact (hY2.mp hi).left
        )).mpr
        apply aux
        clear aux
        exact hY2'

    by_cases h_y2_empty : |Y2| = (0 : num)
    -- If one candidate is empty, then the other is also empty
    · apply V0.se hV0
      constructor
      · rw [h_y2_empty]
        symm
        false_or_by_contra
        rename_i h_y_nonempty
        have aux := pred_exists h_y_nonempty
        obtain ⟨y_witness, ⟨h_y_witness_le, h_y_witness_eq⟩⟩ := aux
        have h_y_witness := V0.l2 hV0 h_y_witness_eq.symm
        have y2_witness := (eq_ext y_witness).mp h_y_witness

        have h_len_y2_gt := V0.l1 hV0 y2_witness
        have h_len_y2_pos := le_lt_trans (V0.b9 hV0 y_witness) h_len_y2_gt
        have h_len_y2_ne_zero := h_len_y2_pos.right
        apply h_len_y2_ne_zero
        exact h_y2_empty.symm
      · intro i hi
        exact (eq_ext i).symm
    -- Two nonempty candidates
    · apply V0.se hV0
      constructor
      -- Prove that the length of two candidates must be the same
      · apply V0.b7 hV0
        -- |Y2| <= |Y|
        · have aux := pred_exists h_y2_empty
          obtain ⟨pred_len_y2, ⟨hpred_len_y2_le, hpred_len_y2_eq⟩⟩ := aux
          rw [hpred_len_y2_eq]
          have pred_len_y2_in_y : pred_len_y2 ∈ Y := by
            rw [eq_ext pred_len_y2]
            apply V0.l2 hV0
            exact hpred_len_y2_eq.symm
          have h_Y_gt := V0.l1 hV0 pred_len_y2_in_y
          rw [V0.b11 hV0]
          apply add_lt_cancel
          exact h_Y_gt
        -- |Y| <= |Y2
        · have aux := pred_exists h_y2_empty
          obtain ⟨pred_len_y2, ⟨hpred_len_y2_le, hpred_len_y2_eq⟩⟩ := aux
          have pred_len_y2_in_y : pred_len_y2 ∈ Y := by
            rw [eq_ext pred_len_y2]
            apply V0.l2 hV0
            exact hpred_len_y2_eq.symm
          have h_Y_gt := V0.l1 hV0 pred_len_y2_in_y
          have h_y_nonempty : ¬ |Y| = (0 : num) := by
            intro h_empty
            rw [h_empty] at h_Y_gt
            exact not_lt_zero h_Y_gt
          have aux := pred_exists h_y_nonempty
          obtain ⟨pred_len_y, ⟨hpred_len_y_le, hpred_len_y_eq⟩⟩ := aux
          have pred_len_y_in_y2 : pred_len_y ∈ Y2 := by
            rw [<- eq_ext pred_len_y]
            apply V0.l2 hV0
            exact hpred_len_y_eq.symm

          have h_Y2_gt := V0.l1 hV0 pred_len_y_in_y2
          rw [V0.b11 hV0]
          rw [hpred_len_y_eq]
          apply add_lt_cancel
          exact h_Y2_gt
      intro i hi
      exact (eq_ext i).symm

open Lean.Expr

set_option pp.rawOnError true

def getProofTerm (thm : Lean.Name) : Lean.MetaM Lean.Expr := do
  let ci ← Lean.getConstInfo thm
  return ci.value!

#check Lean.Expr

def getLenExpr (arg: Lean.Expr) : Lean.MetaM Lean.Expr := do
  let lenTerm <- Lean.Meta.mkAppM ``List.length #[arg]
  let oneTerm := Lean.mkNatLit 1
  let natType := Lean.mkConst ``Nat
  let natAddInst := Lean.mkConst ``instAddNat
  let addFn := Lean.mkConst ``Add.add [Lean.levelZero]
  return Lean.mkAppN addFn #[natType, natAddInst, lenTerm, oneTerm]


-- mkComp (phi : Expr of type (i: num) -> Prop) -> Expression of type (Nat -> List Bool)
-- def comprehension2 (OrigStr : str) :=
--   -- sigma0B formula!
--   let phi (X : str) (i : num) :=
--     (i ∈ X ∧ ∃ j : num, j < i ∧ ¬ j ∈ X)
--     ∨ (¬ i ∈ X ∧ ∀ j : num, j < i → j ∈ X)
--   ∀ y, ∃ X : str, |X| <= y ∧ ∀ z, z < y -> (z ∈ X ↔ phi OrigStr z)

def extractComprehension2 (compArg compLen : Lean.Expr) : Lean.MetaM Lean.Expr := do
  -- extract (|X| + 1)
  let ty <- Lean.Meta.inferType $ compLen.getAppFn.projExpr!
  if isAppOf ty ``Add then
    let ty <- Lean.Meta.inferType $ compLen.getAppArgs[0]!.getAppFn.projExpr!
    if isAppOf ty ``HasLen then
      -- let var := compLen.getAppArgs[0]!.getAppArgs[0]!
      getLenExpr compArg
    else
      Lean.log "string length: bad format!"
      return compArg
  else
    Lean.log "comprehension length: bad format!"
    return compArg

#check Option

def exprListOfBool := (Lean.mkConst ``List [Lean.levelZero]).app $ Lean.mkConst ``Bool

def convTypeIfInteresting (ty : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if ty.isFVar then
    let typeUserName <- Lean.FVarId.getUserName ty.fvarId!
    if typeUserName == `str then
      return some $ exprListOfBool
    else if typeUserName == `num then
      return some $ Lean.mkConst ``Nat
  return none

partial def findExIntro (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  match e with
  | lam name type body binderInfo => do
    let newType <- convTypeIfInteresting type
    let type :=
      match newType with
      | some newType => newType
      | none => type
    Lean.Meta.withLocalDecl name .default type fun x => do
      let newBody <- findExIntro (body.instantiate1 x)
      match newType with
      | some _ => Lean.Meta.mkLambdaFVars #[x] newBody
      | none => return newBody
  | forallE name type body binderInfo => do
    let newType <- convTypeIfInteresting type
    let type :=
      match newType with
      | some newType => newType
      | none => type
    Lean.Meta.withLocalDecl name .default type fun x => do
      let newBody <- findExIntro (body.instantiate1 x)
      match newType with
      | some _ => Lean.Meta.mkForallFVars #[x] newBody
      | none => return newBody
  | letE name type val body nondep => do
    let newType <- convTypeIfInteresting type
    let type :=
      match newType with
      | some newType => newType
      | none => type
    Lean.Meta.withLetDecl name type val (nondep := nondep) fun x => do
      let newBody <- findExIntro (body.instantiate1 x)
      match newType with
      | some _ => Lean.Meta.mkLetFVars #[x] newBody
      | none => return newBody
  | e@(app _ _) => do
    -- TODO: ideally, this case shouldn't be here, really...
    -- we should have something more general
    if isAppOfArity e ``Exists.rec 5 then
      let args := getAppArgsN e 5
      let witness_pair := args[4]!
      let witness <- findExIntro witness_pair
      let raw_intro := args[3]!
      let inst <- Lean.Meta.instantiateLambda raw_intro #[witness]
      return <- findExIntro inst

    -- TODO: same with this. we want to not-detect `Exists.intro`
    -- that proves some sub-lemma. We also potentially want to
    -- detect other ways to construct `Exists` than this specific fn
    -- TODO: this is incorrect already for goal `∃x y, phi(x, y)`
    else if isAppOfArity e ``Exists.intro 4 then
      let args := getAppArgs e
      let witness := args[2]!
      return witness

    -- 2. here, if we see a function application and we need it,
    --    change it to expression calling a function ExtractedFnName(fn)
    let fn := getAppFn e
    let ty <- Lean.Meta.inferType fn
    if isAppOfArity ty ``comprehension2 6 then
      let comp_arg := (getAppArgsN ty 6)[5]!
      let comp_len := (getAppArgsN e 1)[0]!
      return <- extractComprehension2 comp_arg comp_len

    Lean.log "unsuported application!"
    return e
  | e => do
    Lean.log "unsuported expression!"
    return e

-- Assumption 1: we will only work with goals of the form 'exists x'.
-- for goals 't := forall y, exists x..', define: for every y, we can extract from (t y)
-- Assumption 2: the goal needs to be closed using the 'exists' tactic.
-- we only detect Exists.intro

def getInputExpr (X : List Bool) : Lean.Expr :=
  match X with
  | .nil =>
    Lean.mkApp (Lean.mkConst ``List.nil [Lean.levelZero]) (Lean.mkConst ``Bool)
  | .cons h t =>
    let boolType := Lean.mkConst ``Bool
    let headExpr := if h then Lean.mkConst ``true else Lean.mkConst ``false
    let tailExpr := getInputExpr t
    Lean.mkAppN (Lean.mkConst ``List.cons [Lean.levelZero]) #[boolType, headExpr, tailExpr]


def logRaw (e : Lean.Expr) : Lean.MetaM Unit := do
  Lean.withOptions (fun o =>
      o.setBool `pp.notation false
       |>.setBool `pp.all true
       |>.setBool `pp.fullNames true
       |>.setBool `pp.universes true
       |>.setBool `pp.explicit true) do
    Lean.logInfo m!"{← Lean.Meta.ppExpr e}"


open Lean
open Lean.Meta
open Lean.Meta.Tactic


run_meta do
  let term <- getProofTerm ``Succ_total_unique
  let term <- Lean.Meta.reduceAll term
  let extracted <- findExIntro term

  let inp := getInputExpr [false, true, false, true, true, false, true]

  let result <- Lean.Meta.reduce $ extracted.app inp
  IO.println $ result
