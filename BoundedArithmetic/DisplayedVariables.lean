import Mathlib.ModelTheory.Syntax
import BoundedArithmetic.IsEnum
import BoundedArithmetic.Register

open FirstOrder Language

namespace FirstOrder.Language

universe u
variable {L : Language} {α β : Type u}

-- i know it looks stupid but is actually pretty good

class HasVar_x (α : Type*) where x : α
class HasVar_y (α : Type*) where y : α
class HasVar_z (α : Type*) where z : α
class HasDisplayed (α : Type*) extends Subsingleton α where fv : α

instance : IsEnum Empty where
  size := 0
  toIdx := Empty.elim
  fromIdx := Fin.elim0
  to_from_id := by simp only [IsEmpty.forall_iff]
  from_to_id := by simp only [IsEmpty.forall_iff]

inductive Vars1x | x deriving DecidableEq, IsEnum
inductive Vars1y | y deriving DecidableEq, IsEnum
inductive Vars1z | z deriving DecidableEq, IsEnum
inductive Vars2xy | x | y deriving DecidableEq, IsEnum
inductive Vars2xz | x | z deriving DecidableEq, IsEnum
inductive Vars2yz | y | z deriving DecidableEq, IsEnum
inductive Vars3 | x | y | z deriving DecidableEq, IsEnum

instance : HasVar_x Vars1x where x := .x
instance : HasVar_y Vars1y where y := .y
instance : HasVar_z Vars1z where z := .z

instance : HasDisplayed Vars1x where fv := .x; allEq := by exact fun a b ↦ rfl
instance : HasDisplayed Vars1y where fv := .y; allEq := by exact fun a b ↦ rfl
instance : HasDisplayed Vars1z where fv := .z; allEq := by exact fun a b ↦ rfl

instance [HasDisplayed α] : IsEnum α where
  size := 1
  toIdx _ := 0
  fromIdx _ := HasDisplayed.fv
  to_from_id id := by rw [Fin.eq_zero id]
  from_to_id elt := by subsingleton

deriving instance IsEnum for Vars1x
deriving instance IsEnum for Vars1y
deriving instance IsEnum for Vars1z

instance : HasVar_x Vars2xy where x := Vars2xy.x
instance : HasVar_y Vars2xy where y := Vars2xy.y
instance : HasVar_x Vars2xz where x := Vars2xz.x
instance : HasVar_z Vars2xz where z := Vars2xz.z
instance : HasVar_y Vars2yz where y := Vars2yz.y
instance : HasVar_z Vars2yz where z := Vars2yz.z

instance : HasVar_x Vars3 where x := Vars3.x
instance : HasVar_y Vars3 where y := Vars3.y
instance : HasVar_z Vars3 where z := Vars3.z

namespace IsEnum.size
@[delta0_simps] lemma Empty   : IsEnum.size Empty   = 0 := rfl
@[delta0_simps] lemma Vars1x  : IsEnum.size Vars1x  = 1 := rfl
@[delta0_simps] lemma Vars1y  : IsEnum.size Vars1y  = 1 := rfl
@[delta0_simps] lemma Vars1z  : IsEnum.size Vars1z  = 1 := rfl
@[delta0_simps] lemma Vars2xy : IsEnum.size Vars2xy = 2 := rfl
@[delta0_simps] lemma Vars2xz : IsEnum.size Vars2xz = 2 := rfl
@[delta0_simps] lemma Vars2yz : IsEnum.size Vars2yz = 2 := rfl
@[delta0_simps] lemma Vars3   : IsEnum.size Vars3   = 3 := rfl
end IsEnum.size

namespace IsEnum.toIdx
@[delta0_simps] lemma Empty : IsEnum.toIdx (α := Empty) = Empty.elim := rfl
@[delta0_simps] lemma Vars1x_x : IsEnum.toIdx Vars1x.x = 0 := rfl
@[delta0_simps] lemma Vars1y_y : IsEnum.toIdx Vars1y.y = 0 := rfl
@[delta0_simps] lemma Vars1z_z : IsEnum.toIdx Vars1z.z = 0 := rfl
@[delta0_simps] lemma Vars2xy_x : IsEnum.toIdx Vars2xy.x = 0 := rfl
@[delta0_simps] lemma Vars2xy_y : IsEnum.toIdx Vars2xy.y = 1 := rfl
@[delta0_simps] lemma Vars2xz_x : IsEnum.toIdx Vars2xz.x = 0 := rfl
@[delta0_simps] lemma Vars2xz_z : IsEnum.toIdx Vars2xz.z = 1 := rfl
@[delta0_simps] lemma Vars2yz_y : IsEnum.toIdx Vars2yz.y = 0 := rfl
@[delta0_simps] lemma Vars2yz_z : IsEnum.toIdx Vars2yz.z = 1 := rfl
@[delta0_simps] lemma Vars3_x : IsEnum.toIdx Vars3.x = 0 := rfl
@[delta0_simps] lemma Vars3_y : IsEnum.toIdx Vars3.y = 1 := rfl
@[delta0_simps] lemma Vars3_z : IsEnum.toIdx Vars3.z = 2 := rfl
end IsEnum.toIdx

@[delta0_simps] def x {k} [h : HasVar_x α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.x)
@[delta0_simps] def y {k} [h : HasVar_y α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.y)
@[delta0_simps] def z {k} [h : HasVar_z α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.z)
namespace x
@[delta0_simps] lemma _1x {k} : x (α := Vars1x) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .x) := by rfl
@[delta0_simps] lemma _2xy {k} : x (α := Vars2xy) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .x) := by rfl
@[delta0_simps] lemma _2xz {k} : x (α := Vars2xz) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .x) := by rfl
@[delta0_simps] lemma _3 {k} : x (α := Vars3) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .x) := by rfl
end x
namespace y
@[delta0_simps] lemma _1y {k} : y (α := Vars1y) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
@[delta0_simps] lemma _2xy {k} : y (α := Vars2xy) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
@[delta0_simps] lemma _2yz {k} : y (α := Vars2yz) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
@[delta0_simps] lemma _3 {k} : y (α := Vars3) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
end y
namespace z
@[delta0_simps] lemma _1z {k} : z (α := Vars1z) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .z) := by rfl
@[delta0_simps] lemma _2xz {k} : z (α := Vars2xz) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .z) := by rfl
@[delta0_simps] lemma _2yz {k} : z (α := Vars2yz) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .z) := by rfl
@[delta0_simps] lemma _3 {k} : z (α := Vars3) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .z) := by rfl
end z

namespace BoundedFormula
variable {disp : Type u} [HasDisplayed disp]

@[delta0_simps]
def display (phi : L.Formula disp) : L.Formula (disp ⊕ Empty) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | HasDisplayed.fv => Sum.inl HasDisplayed.fv
    )
    invFun := (fun fv => match fv with | .inl _ => HasDisplayed.fv)
    left_inv := by
      intro v
      simp only
      subsingleton
    right_inv := by
      intro v; cases v; simp only; congr; subsingleton
      apply Empty.elim; assumption
  }

namespace display

@[delta0_simps]
theorem imp (φ ψ : L.Formula disp) :
    (φ.imp ψ).display = (φ.display).imp (ψ.display) :=
  rfl
end display

@[delta0_simps] def display_x_x (phi : L.Formula Vars1x) : L.Formula (Vars1x ⊕ Empty) := display phi
@[delta0_simps] def display_y_y (phi : L.Formula Vars1y) : L.Formula (Vars1y ⊕ Empty) := display phi
@[delta0_simps] def display_z_z (phi : L.Formula Vars1z) : L.Formula (Vars1z ⊕ Empty) := display phi

@[delta0_simps]
def display_x_xy (phi : L.Formula Vars2xy) : L.Formula (Vars1x ⊕ Vars1y) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .x => Sum.inl .x
    | .y => Sum.inr .y
    ),
    invFun := (fun fv => match fv with | .inl _ => .x | .inr _ => .y)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, and_self]
  }

@[delta0_simps]
def display_x_xz (phi : L.Formula Vars2xz) : L.Formula (Vars1x ⊕ Vars1z) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .x => Sum.inl .x
    | .z => Sum.inr .z
    )
    invFun := (fun fv => match fv with | .inl _ => .x | .inr _ => .z)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, and_self]
  }

@[delta0_simps]
def display_y_xy (phi : L.Formula Vars2xy) : L.Formula (Vars1y ⊕ Vars1x) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .x => Sum.inr .x
    | .y => Sum.inl .y
    ),
    invFun := (fun fv => match fv with | .inr _ => .x | .inl _ => .y)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, and_self]
  }

@[delta0_simps]
def display_y_yz (phi : L.Formula Vars2yz) : L.Formula (Vars1y ⊕ Vars1z) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .y => Sum.inl .y
    | .z => Sum.inr .z
    ),
    invFun := (fun fv => match fv with | .inl _ => .y | .inr _ => .z)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, and_self]
  }

@[delta0_simps]
def display_z_xz (phi : L.Formula Vars2xz) : L.Formula (Vars1z ⊕ Vars1x) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inr .x
      | .z => Sum.inl .z)
    invFun := (fun fv => match fv with
      | .inl _ => .z
      | .inr _ => .x)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall,
        implies_true, and_self]
  }

@[delta0_simps]
def display_z_yz (phi : L.Formula Vars2yz) : L.Formula (Vars1z ⊕ Vars1y) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .y => Sum.inr .y
      | .z => Sum.inl .z)
    invFun := (fun fv => match fv with
      | .inl _ => .z
      | .inr _ => .y)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall,
        implies_true, and_self]
  }

@[delta0_simps]
def display_x_xyz (phi : L.Formula Vars3) : L.Formula (Vars1x ⊕ Vars2yz) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inl .x
      | .y => Sum.inr .y
      | .z => Sum.inr .z)
    invFun := (fun fv => match fv with
      | .inl _    => .x
      | .inr .y   => .y
      | .inr .z   => .z)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_y_xyz (phi : L.Formula Vars3) : L.Formula (Vars1y ⊕ Vars2xz) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inr .x
      | .y => Sum.inl .y
      | .z => Sum.inr .z)
    invFun := (fun fv => match fv with
      | .inl _    => .y
      | .inr .x   => .x
      | .inr .z   => .z)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_z_xyz (phi : L.Formula Vars3) : L.Formula (Vars1z ⊕ Vars2xy) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inr .x
      | .y => Sum.inr .y
      | .z => Sum.inl .z)
    invFun := (fun fv => match fv with
      | .inl _    => .z
      | .inr .x   => .x
      | .inr .y   => .y)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def flip (phi : L.Formula (α ⊕ β)) : L.Formula (β ⊕ α) :=
  phi.relabelEquiv {
    toFun := Sum.swap (α := α) (β := β)
    invFun := Sum.swap
    left_inv := Sum.swap_leftInverse
    right_inv := Sum.swap_rightInverse
  }

end BoundedFormula

end FirstOrder.Language
