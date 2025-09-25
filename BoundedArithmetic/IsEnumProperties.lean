import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import BoundedArithmetic.IsEnum

-- namespace List
-- theorem ofFn_eq_pmap {α n} {f : Fin n → α} :
--     ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
--   rw [pmap_eq_map_attach]
--   exact ext_get (by simp) fun i hi1 hi2 => by simp [get_ofFn f ⟨i, hi1⟩]
-- #align list.of_fn_eq_pmap List.ofFn_eq_pmap

-- theorem nodup_ofFn_ofInjective {α n} {f : Fin n → α} (hf : Function.Injective f) :
--     Nodup (ofFn f) := by
--   rw [ofFn_eq_pmap]
--   exact (nodup_range n).pmap fun _ _ _ _ H => Fin.val_eq_of_eq <| hf H
-- #align list.nodup_of_fn_of_injective List.nodup_ofFn_ofInjective
-- end List

namespace IsEnum
variable {α} {enum : IsEnum α}


def left_inv : Function.LeftInverse enum.fromIdx enum.toIdx :=
  enum.from_to_id

def right_inv : Function.RightInverse enum.fromIdx enum.toIdx :=
  enum.to_from_id

def equiv : α ≃ Fin (enum.size) where
  toFun := enum.toIdx
  invFun := enum.fromIdx
  left_inv := left_inv
  right_inv := right_inv

instance : Finite α := @Finite.intro _ (enum.size) equiv

def fromIdx_injective : Function.Injective enum.fromIdx := Function.LeftInverse.injective right_inv
def toIdx_injective : Function.Injective enum.toIdx := Function.LeftInverse.injective left_inv

-- Inspired by Mathlib.Data.Finset.Dedup.lean; toList, nodup_toList...
-- https://github.com/leanprover-community/mathlib4/blob/f4506f7151c9057fd9f8714b2a1f13a647fe2352/Mathlib/Data/Finset/Dedup.lean#L162-L164
section ToList
def toList : List α := List.ofFn enum.fromIdx

theorem nodup_toList : enum.toList.Nodup := by
  unfold List.Nodup
  unfold toList
  rw [List.pairwise_ofFn]
  intro i j hij
  apply Function.Injective.ne fromIdx_injective
  exact Fin.ne_of_lt hij

end ToList

end IsEnum
