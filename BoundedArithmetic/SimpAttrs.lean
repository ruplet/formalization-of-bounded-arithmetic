import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Semantics

import BoundedArithmetic.IsEnum
import BoundedArithmetic.IsEnumProperties
import BoundedArithmetic.AxiomSchemes
import BoundedArithmetic.Syntax
import BoundedArithmetic.Complexity
import BoundedArithmetic.Order
import BoundedArithmetic.Register
import BoundedArithmetic.AxiomSchemes

open FirstOrder
open Language
open BoundedFormula

attribute [delta0_simps]
  Sentence.Realize Formula.Realize mkInductionSentence Formula.iAlls' BoundedFormula.alls
  display_z_xyz  x y z relabelEquiv.eq Equiv.coe_fn_mk
   BoundedFormula.flip display relabelEquiv.imp relabelEquiv.all Nat.reduceAdd
  relabel_imp Nat.add_zero relabel_all Nat.add_eq BoundedFormula.realize_imp Formula.realize_imp realize_subst
  peano.realize_zero_to_zero realize_all Nat.succ_eq_add_one BoundedFormula.realize_relabel Formula.realize_relabel Fin.castAdd_zero
  Fin.cast_refl Function.comp_id realize_bdEqual Term.realize_relabel
  peano.realize_add_to_add Term.realize_var Function.comp_apply Sum.map_inl Sum.elim_inl
  Sum.map_inr  Fin.isValue Sum.elim_inr Fin.snoc Fin.coe_ofNat_eq_mod
  Nat.zero_mod zero_lt_one  Fin.reduceLast Fin.zero_eq_one_iff OfNat.ofNat_ne_one
  not_false_eq_true Fin.castLT_eq_castPred Fin.castPred_zero Fin.castSucc_zero
  Fin.val_eq_zero lt_self_iff_false cast_eq  Nat.mod_succ id_eq
  Fin.snoc_comp_castAdd Fin.snoc_comp_natAdd realize_relabelEquiv Fin.natAdd_eq_addNat
  Fin.addNat_one Fin.succ_zero_eq_one Fin.reduceNatAdd Sum.swap_inl
  Fin.reduceCastAdd peano.realize_one_to_one BoundedFormula.exs Sentence.Realize Formula.Realize Formula.relabel Fin.snoc
  Sentence.Realize Formula.Realize mkInductionSentence Formula.iAlls' alls
   display_z_xyz peano.instAddTerm x y z relabelEquiv.eq Equiv.coe_fn_mk
   BoundedFormula.flip display relabelEquiv.imp relabelEquiv.all Nat.reduceAdd
  relabel_imp Nat.add_zero relabel_all Nat.add_eq realize_imp realize_subst
  peano.realize_zero_to_zero realize_all Nat.succ_eq_add_one realize_relabel Fin.castAdd_zero
  Fin.cast_refl Function.comp_id realize_bdEqual Term.realize_relabel
  peano.realize_add_to_add Term.realize_var Function.comp_apply Sum.map_inl Sum.elim_inl
  Sum.map_inr  Fin.isValue Sum.elim_inr Fin.snoc Fin.coe_ofNat_eq_mod
  Nat.zero_mod zero_lt_one reduceDIte Fin.reduceLast Fin.zero_eq_one_iff OfNat.ofNat_ne_one
  not_false_eq_true Fin.castLT_eq_castPred Fin.castPred_zero Fin.castSucc_zero
  Fin.val_eq_zero lt_self_iff_false cast_eq  Nat.mod_succ id_eq
  Fin.snoc_comp_castAdd Fin.snoc_comp_natAdd realize_relabelEquiv Fin.natAdd_eq_addNat
  Fin.addNat_one Fin.succ_zero_eq_one Fin.reduceNatAdd Sum.swap_inl
  Fin.reduceCastAdd peano.realize_one_to_one  Fin.snoc
  peano.instMulTerm peano.realize_mul_to_mul Term.realize_var Function.comp_apply
    Sum.map_inl Sum.elim_inl Sum.map_inr  Fin.isValue Sum.elim_inr Fin.snoc
    Nat.reduceAdd Fin.coe_ofNat_eq_mod Nat.zero_mod zero_lt_one reduceDIte Fin.reduceLast
    Fin.zero_eq_one_iff  OfNat.ofNat_ne_one not_false_eq_true
    Fin.castLT_eq_castPred Fin.castPred_zero Fin.castSucc_zero
    lt_self_iff_false cast_eq peano.realize_add_to_add  Nat.mod_succ id_eq
    Fin.natAdd_eq_addNat Fin.addNat_one Fin.succ_zero_eq_one Fin.reduceNatAdd Sum.swap_inl
     Fin.reduceCastAdd

  realize_not realize_bot realize_top realize_inf realize_imp realize_rel realize_sup realize_inf
  realize_relabel
