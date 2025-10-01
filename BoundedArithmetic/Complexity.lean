import Mathlib.ModelTheory.Complexity

import BoundedArithmetic.DisplayedVariables
import BoundedArithmetic.Order
import BoundedArithmetic.LanguagePeano
import BoundedArithmetic.LanguageZambella

open FirstOrder Language BoundedFormula Formula

universe u
variable {L : Language} [IsOrdered L] {a : Type u}


namespace FirstOrder.Language.BoundedFormula

namespace IsAtomic

@[delta0_simps]
theorem relabelEquiv.mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m}
    (f : α ≃ β) (h : φ.IsAtomic) : (φ.relabelEquiv f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem relabelEquiv.mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : (φ.relabelEquiv f).IsAtomic)
     : φ.IsAtomic :=
  sorry

theorem relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsAtomic <-> φ.IsAtomic :=
  ⟨relabelEquiv.mpr f, relabelEquiv.mp f⟩

@[delta0_simps]
theorem display {disp} [HasDisplayed disp] (phi : L.Formula disp):
  phi.display.IsAtomic <-> phi.IsAtomic :=
by
  unfold BoundedFormula.display
  rw [relabelEquiv]

end IsAtomic


-- Definition 3.7, page 36 of draft (47 of pdf)
abbrev IsOpen {a} {n} (formula : L.BoundedFormula a n) := IsQF formula

namespace IsOpen

omit [IsOrdered L] in
@[delta0_simps]
theorem equal {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1.bdEqual t2).IsOpen :=
by
  constructor
  apply IsAtomic.equal

@[delta0_simps]
theorem relabelEquiv {a b} {g : a ≃ b} (phi : L.Formula a):
  (phi.relabelEquiv g).IsOpen <-> phi.IsOpen :=
by
  constructor <;> intro h
  · -- dependent elimination failed on 'cases h' :(((
    sorry
  · cases h with
    | falsum =>
      rw [relabelEquiv.falsum]
      exact IsQF.falsum
    | of_isAtomic h =>
      constructor
      rw [IsAtomic.relabelEquiv]
      exact h
    | imp hphi hpsi =>
      rw [relabelEquiv.imp]
      apply IsQF.imp
        <;> rw [<- IsOpen]
        <;> rw [IsOpen.relabelEquiv]
        <;> assumption

@[delta0_simps]
theorem display {disp} [HasDisplayed disp] (phi : L.Formula disp):
    phi.display.IsOpen <-> phi.IsOpen := by
  unfold BoundedFormula.display
  rw [relabelEquiv]

end IsOpen



-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
inductive IsDelta0 : {n : Nat} -> L.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsDelta0 phi1) (h2 : IsDelta0 phi2) : IsDelta0 (phi1.imp phi2)
| bdEx
  {disp} [HasDisplayed disp]
  (phi : L.Formula (a ⊕ disp))
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 $ iBdEx' t phi

| bdAll
  {disp} [HasDisplayed disp]
  (phi : L.Formula (a ⊕ disp))
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 $ iBdAll' t phi
| of_isQF {phi} (h : IsQF phi) : IsDelta0 phi



-- THIS IS NOT TRUE!
-- @[simp]
-- theorem not_inf {L : Language} {α} {k} (φ ψ : L.BoundedFormula α k) :
--   (φ ⊓ ψ).not = (φ.not) ⊔ (ψ.not) := by
--   unfold min instMin max instMax
--   simp only
--   unfold BoundedFormula.not



namespace IsQF

@[delta0_simps]
theorem imp.mpr {L : Language} {α} {m} {φ ψ : L.BoundedFormula α m} :
    (φ.imp ψ).IsQF <-> (φ.IsQF ∧ ψ.IsQF) := by
  constructor
  · intro h
    constructor
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact pre
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact post
  · intro h
    apply IsQF.imp h.left h.right

@[delta0_simps]
theorem relabelEquiv.mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : φ.IsQF) :
  (φ.relabelEquiv f).IsQF := by
  sorry

@[delta0_simps]
theorem relabelEquiv.mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) (h : (φ.relabelEquiv f).IsQF) :
    φ.IsQF := by
  sorry

@[delta0_simps]
theorem relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsQF <-> φ.IsQF := ⟨IsQF.relabelEquiv.mpr f, IsQF.relabelEquiv.mp f⟩

-- @[delta0_simps]
-- theorem mapTermRel {α β} {m : ℕ} {φ : peano.BoundedFormula α 0} {g : Nat -> Nat}  (ft: forall n, peano.Term (α ⊕ (Fin n)) -> peano.Term (β ⊕ Fin (g n))) (fr) (h) :
--   (φ.mapTermRel ft fr h).IsQF <-> φ.IsQF := by
--   sorry

end IsQF


namespace IsDelta0


-- Ex x < 7, phi(x) := ~All x, ~(x < 7 and phi(x))
-- NONE OF THESE THEOREMS ARE TRUE WHEN WE DON'T ALLOW


-- failed attempt at proving (false) theorem IsDelta (p->q) -> IsDelta p, IsDelta q
-- -- omit [L.IsOrdered] in
-- -- theorem trans {β n k} : L.BoundedFormula β (n + 1 + k) = L.BoundedFormula β (n + k + 1) := by
-- --   conv => lhs; arg 3; rw [add_assoc]; arg 2; rw [add_comm]
-- --   conv => rhs; arg 3; rw [add_assoc]

-- -- omit [L.IsOrdered] in
-- -- variable {α β n} in
-- -- @[simp]
-- -- theorem relabel_all (g : α → β ⊕ (Fin (n + 1))) {k} (φ : L.BoundedFormula α k) :
-- --     φ.all.relabel g = (trans ▸ φ.relabel g).all := by
-- --   rw [relabel, mapTermRel, relabel]
-- --   simp

-- theorem imp.mp {a} {n} (phi psi : peano.BoundedFormula a n) : IsDelta0 phi -> IsDelta0 psi -> IsDelta0 (phi.imp psi) := by
--   intro hphi hpsi
--   apply IsDelta0.imp
--   · sorry
--     -- fix universe polymorphism
--     -- exact hphi
--   · sorry

-- -- This theorem is not true anymore when NOT modifying ModelTheory,
-- -- i.e. when phi.ex = phi.not.all.not
-- theorem imp.mpr {a} {n} (phi psi : peano.BoundedFormula a n) : (IsDelta0 phi ∧ IsDelta0 psi) <-> IsDelta0 (phi.imp psi) := by
--   apply Iff.intro
--   · intro h
--     apply IsDelta0.imp
--     · exact h.left
--     · exact h.right
--   · intro h
--     cases h with
--     | of_isQF h' =>
--       cases h' with
--       | of_isAtomic h'' =>
--         cases h''
--       | imp hPhi hPsi =>
--         apply And.intro
--         · apply IsDelta0.of_isQF; exact hPhi
--         · apply IsDelta0.of_isQF; exact hPsi
--     | imp hPhi hPsi =>
--       apply And.intro
--       · exact hPhi
--       · exact hPsi
--     | bdEx phi t =>
--       constructor
--       · simp only [<- relabel_not]
--         -- PROBLEM: relabel_all requires BoundedFormula α (>=1), but i have 0!
--         rw [relabel_not]
--         rw [relabel_inf]
--         -- NOW, THIS IS NOT TRUE! (UNPROVABLE): we cannot move this negation
--         -- deeper into the formula. neither move relabel out.
--         -- definition of IDelta0 has to be altered!
--         rw [not_inf]
--         conv => arg 1; rw [<- relabel_all]



--         apply IsDelta0.bdAll
--       · apply IsDelta0.of_isQF
--         constructor


-- theorem not {a} {n} (phi : peano.BoundedFormula a n) : IsDelta0 phi <-> IsDelta0 phi.not := by
--   apply Iff.intro
--   · intro h
--     unfold BoundedFormula.not
--     apply IsDelta0.imp
--     · exact h
--     · constructor
--       constructor
--   · unfold BoundedFormula.not
--     intro h
--     cases h with
--     | imp hphi hpsi =>
--       exact hphi
--     | bdEx phi t

--     rw [<- IsDelta0.imp.mpr]
--     intro h
--     exact h.left

@[delta0_simps]
theorem bot {a n} : (⊥ : L.BoundedFormula a n).IsDelta0  := by
  constructor
  exact isQF_bot

@[delta0_simps]
theorem equal {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1.bdEqual t2).IsDelta0 :=
by
  constructor
  constructor
  apply IsAtomic.equal

@[delta0_simps]
theorem neq {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1 ≠' t2).IsDelta0 :=
by
  constructor
  apply equal
  apply bot

@[delta0_simps]
theorem min {a} {n} (phi psi : L.BoundedFormula a n) :
  IsDelta0 (phi ⊓ psi) <-> (IsDelta0 phi ∧ IsDelta0 psi) :=
by
  constructor
  · intro h
    have h' : IsDelta0 ((phi ⟹ ∼psi) ⟹ ⊥) := by
      simpa only using h
    sorry
    -- cases h with
    -- | imp h' _ =>
    --   cases h' with
    --   | imp hphi hpsi =>
    --     cases hpsi with
    --     | imp hpsi' =>
    --       exact ⟨hphi, hpsi'⟩
  · rintro ⟨hφ, hψ⟩
    constructor; constructor; assumption; constructor; assumption; exact bot; exact bot

-- theorem max {a} {n} (phi psi : peano.BoundedFormula a n) : (IsDelta0 phi ∧ IsDelta0 psi) <-> IsDelta0 (phi ⊔ psi) := by
--   unfold Max.max instMax
--   simp only
--   constructor
--   · intro h
--     constructor
--     rw [<- not]
--     exact h.left
--     exact h.right
--   · intro h
--     cases h with
--     | imp hNotPhi hPsi => rw [<- not] at hNotPhi; constructor <;> assumption
--     | of_isQF h =>

--       cases h with | of_isAtomic h =>

--   rw [<- IsDelta0.imp.mpr]
--   rw [<- IsDelta0.not]

-- theorem foldr_inf {α} {n} (l : List (peano.BoundedFormula α n)) :
--   (l.foldr (· ⊓ ·) ⊤).IsDelta0 ↔ ∀ φ ∈ l, φ.IsDelta0 := by
--   induction l with
--   | nil =>
--     simp only [List.foldr_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
--     apply IsDelta0.of_isQF
--     exact IsQF.top
--   | cons φ l ih =>
--     simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
--     constructor
--     · intro h
--       rw [<- min] at h
--       constructor
--       · exact h.left
--       · apply ih.mp
--         exact h.right
--     · intro h
--       rw [<- min]
--       constructor
--       · exact h.left
--       · apply ih.mpr
--         exact h.right

-- theorem iInf' {α β} {n} [IsEnum β] (f : β -> peano.BoundedFormula α n) :
--   (BoundedFormula.iInf' f).IsDelta0 ↔ ∀ b, (f b).IsDelta0 := by
--   unfold BoundedFormula.iInf'
--   rw [IsDelta0.foldr_inf]
--   unfold IsEnum.toList
--   simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--   constructor
--   · simp only [List.mem_ofFn]
--     intro h b
--     specialize h b
--     apply h
--     exists IsEnum.toIdx b
--     exact IsEnum.from_to_id b
--   · simp only [List.mem_ofFn]
--     intro h _ _
--     apply h

-- @[delta0_simps]
-- theorem iBdEx' {a b} [HasDisplayed b] {bdTerm} {phi : peano.Formula (a ⊕ b)}
--   : IsDelta0 $ (Formula.iBdEx' bdTerm phi : peano.BoundedFormula a 0) := by
--   apply IsDelta0.bdEx

--   unfold Formula.iBdEx'
--   unfold Formula.iExs'
--   unfold BoundedFormula.exs
--   unfold BoundedFormula.exs
--   simp only
--   simp only [relabel.inf, Nat.add_zero]
--   apply IsDelta0.bdEx



-- @[delta0_simps]
-- theorem mapTermRel {α β} (φ : peano.BoundedFormula α 0) {g : Nat -> Nat} {ft: forall n, peano.Term (α ⊕ (Fin n)) -> peano.Term (β ⊕ Fin (g n))} {fr} {h}:
--     (φ.mapTermRel ft fr h).IsDelta0 <-> φ.IsDelta0 := by
--   sorry

@[delta0_simps]
theorem relabelEquiv {a b} (phi : peano.Formula a) (g : a ≃ b):
  BoundedFormula.IsDelta0 phi <-> BoundedFormula.IsDelta0 (phi.relabelEquiv g) :=
by
  cases phi with
  | falsum =>
    apply Iff.intro <;> (intro; constructor; constructor)
  | equal =>
    apply Iff.intro <;> (intro; constructor; constructor; constructor)
  | imp p q =>
    sorry
  | rel =>
    constructor <;> (intro; constructor; constructor; constructor)
  -- | ex => sorry
  | all => sorry



end IsDelta0




-- inductive IsDelta0 : {n : Nat} -> L.BoundedFormula a n -> Prop
-- | imp {phi1 phi2} (h1 : IsDelta0 phi1) (h2 : IsDelta0 phi2) : IsDelta0 (phi1.imp phi2)
-- | bdEx
--   {disp} [HasDisplayed disp]
--   (phi : L.Formula (a ⊕ disp))
--   (t : L.Term (a ⊕ Fin 0))
--   : IsDelta0 $ iBdEx' t phi

-- | bdAll
--   {disp} [HasDisplayed disp]
--   (phi : L.Formula (a ⊕ disp))
--   (t : L.Term (a ⊕ Fin 0))
--   : IsDelta0 $ iBdAll' t phi
-- | of_isQF {phi} (h : IsQF phi) : IsDelta0 phi


-- only bounded number quantifiers allowed. and free string vars.
-- p. 82 of pdf of Logical Foundatoin release
inductive IsSigma0B : {n : Nat} -> zambella.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsSigma0B phi1) (h2 : IsSigma0B phi2)
  : IsSigma0B (phi1.imp phi2)
| bdEx
  {disp} [hd : HasDisplayed disp]
  (phi : zambella.Formula (a ⊕ disp))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdEx' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ hd.fv]) ⊓ phi)
| bdAll
  {disp} [hd : HasDisplayed disp]
  (phi : zambella.Formula (a ⊕ disp))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdAll' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ hd.fv]) ⊓ phi)
| bdAllLt
  {disp} [hd : HasDisplayed disp]
  (phi : zambella.Formula (a ⊕ disp))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B $ iBdAllLt' t ((rel ZambellaRel.isnum ![var $ Sum.inl $ Sum.inr $ hd.fv]) ⊓ phi)

| of_isQF {phi} (h : IsQF phi) : IsSigma0B phi


namespace Sigma0B

@[delta0_simps]
theorem relabelEquiv {a b} {g : a ≃ b} (phi : zambella.Formula a):
  (phi.relabelEquiv g).IsSigma0B <-> phi.IsSigma0B :=
by
  sorry

end Sigma0B

end FirstOrder.Language.BoundedFormula
