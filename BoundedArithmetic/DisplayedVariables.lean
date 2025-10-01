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

-- BEGIN UGLY ADDITION
class HasVar_X (α : Type*) where X : α

inductive Vars1X | X deriving DecidableEq, IsEnum
inductive Vars3X | x | y | z | X deriving DecidableEq, IsEnum
inductive Vars2xyX | x | y | X deriving DecidableEq, IsEnum
inductive Vars2yX | y | X deriving DecidableEq, IsEnum
inductive Vars2yzX | y | z | X deriving DecidableEq, IsEnum

@[delta0_simps] instance : HasVar_x Vars3X where x := .x
@[delta0_simps] instance : HasVar_y Vars3X where y := .y
@[delta0_simps] instance : HasVar_z Vars3X where z := .z
@[delta0_simps] instance : HasVar_x Vars2xyX where x := .x
@[delta0_simps] instance : HasVar_y Vars2xyX where y := .y
@[delta0_simps] instance : HasVar_y Vars2yzX where y := .y
@[delta0_simps] instance : HasVar_z Vars2yzX where z := .z
@[delta0_simps] instance : HasVar_y Vars2yX where y := .y

@[delta0_simps] instance : HasVar_X Vars1X where X := .X
@[delta0_simps] instance : HasVar_X Vars3X where X := .X
@[delta0_simps] instance : HasVar_X Vars2xyX where X := .X
@[delta0_simps] instance : HasVar_X Vars2yX where X := .X
@[delta0_simps] instance : HasVar_X Vars2yzX where X := .X


@[delta0_simps] def X {k} [h : HasVar_X α]: L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.X)
instance : HasDisplayed Vars1X where fv := .X; allEq := by exact fun a b ↦ rfl

namespace IsEnum.size
@[delta0_simps] lemma Vars1X     : IsEnum.size Vars1X   = 1 := rfl
@[delta0_simps] lemma Vars3X     : IsEnum.size Vars3X   = 4 := rfl
@[delta0_simps] lemma Vars2xyX   : IsEnum.size Vars2xyX   = 3 := rfl
@[delta0_simps] lemma Vars2yzX   : IsEnum.size Vars2yzX   = 3 := rfl
@[delta0_simps] lemma Vars2yX   : IsEnum.size Vars2yX   = 2 := rfl
end IsEnum.size

namespace IsEnum.toIdx
@[delta0_simps] lemma Vars1X     : IsEnum.toIdx Vars1X.X   = 0 := rfl
@[delta0_simps] lemma Vars3X_x   : IsEnum.toIdx Vars3X.x   = 0 := rfl
@[delta0_simps] lemma Vars3X_y   : IsEnum.toIdx Vars3X.y   = 1 := rfl
@[delta0_simps] lemma Vars3X_z   : IsEnum.toIdx Vars3X.z   = 2 := rfl
@[delta0_simps] lemma Vars3X_X   : IsEnum.toIdx Vars3X.X   = 3 := rfl
@[delta0_simps] lemma Vars2xyX_x   : IsEnum.toIdx Vars2xyX.x   = 0 := rfl
@[delta0_simps] lemma Vars2xyX_y   : IsEnum.toIdx Vars2xyX.y   = 1 := rfl
@[delta0_simps] lemma Vars2xyX_X   : IsEnum.toIdx Vars2xyX.X   = 2 := rfl
@[delta0_simps] lemma Vars2yzX_y   : IsEnum.toIdx Vars2yzX.y   = 0 := rfl
@[delta0_simps] lemma Vars2yzX_z   : IsEnum.toIdx Vars2yzX.z   = 1 := rfl
@[delta0_simps] lemma Vars2yzX_X   : IsEnum.toIdx Vars2yzX.X   = 2 := rfl
@[delta0_simps] lemma Vars2yX_y   : IsEnum.toIdx Vars2yX.y   = 0 := rfl
@[delta0_simps] lemma Vars2yX_X   : IsEnum.toIdx Vars2yX.X   = 1 := rfl
end IsEnum.toIdx
-- END

@[delta0_simps] instance : HasVar_x Vars1x where x := .x
@[delta0_simps] instance : HasVar_y Vars1y where y := .y
@[delta0_simps] instance : HasVar_z Vars1z where z := .z

@[delta0_simps] instance : HasDisplayed Vars1x where fv := .x; allEq := by exact fun a b ↦ rfl
@[delta0_simps] instance : HasDisplayed Vars1y where fv := .y; allEq := by exact fun a b ↦ rfl
@[delta0_simps] instance : HasDisplayed Vars1z where fv := .z; allEq := by exact fun a b ↦ rfl

instance [HasDisplayed α] : IsEnum α where
  size := 1
  toIdx _ := 0
  fromIdx _ := HasDisplayed.fv
  to_from_id id := by rw [Fin.eq_zero id]
  from_to_id elt := by subsingleton

@[delta0_simps] instance : HasVar_x Vars2xy where x := Vars2xy.x
@[delta0_simps] instance : HasVar_y Vars2xy where y := Vars2xy.y
@[delta0_simps] instance : HasVar_x Vars2xz where x := Vars2xz.x
@[delta0_simps] instance : HasVar_z Vars2xz where z := Vars2xz.z
@[delta0_simps] instance : HasVar_y Vars2yz where y := Vars2yz.y
@[delta0_simps] instance : HasVar_z Vars2yz where z := Vars2yz.z

@[delta0_simps] instance : HasVar_x Vars3 where x := Vars3.x
@[delta0_simps] instance : HasVar_y Vars3 where y := Vars3.y
@[delta0_simps] instance : HasVar_z Vars3 where z := Vars3.z

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

-- BEGIN UGLY ADDITION
namespace x
@[delta0_simps] lemma _2xyX {k} : x (α := Vars2xyX) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .x) := by rfl
end x

namespace y
@[delta0_simps] lemma _2xyX {k} : y (α := Vars2xyX) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
@[delta0_simps] lemma _2yzX {k} : y (α := Vars2yzX) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
@[delta0_simps] lemma _2yX {k} : y (α := Vars2yX) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .y) := by rfl
end y

namespace z
@[delta0_simps] lemma _2yzX {k} : z (α := Vars2yzX) = (L.var (α := _ ⊕ Fin k) $ Sum.inl .z) := by rfl
end z
-- END

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

-- BEGIN UGLY ADDITION...
@[delta0_simps]
def display_x_xyzX (phi : L.Formula Vars3X) : L.Formula (Vars1x ⊕ Vars2yzX) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inl .x
      | .y => Sum.inr .y
      | .z => Sum.inr .z
      | .X => Sum.inr .X)
    invFun := (fun fv => match fv with
      | .inl _    => .x
      | .inr .y   => .y
      | .inr .z   => .z
      | .inr .X   => .X)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_z_xyzX (phi : L.Formula Vars3X) : L.Formula (Vars1z ⊕ Vars2xyX) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .x => Sum.inr .x
      | .y => Sum.inr .y
      | .z => Sum.inl .z
      | .X => Sum.inr .X)
    invFun := (fun fv => match fv with
      | .inl _    => .z
      | .inr .y   => .y
      | .inr .x   => .x
      | .inr .X   => .X)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_X_yzX (phi : L.Formula Vars2yzX) : L.Formula (Vars1X ⊕ Vars2yz) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .y => Sum.inr .y
      | .z => Sum.inr .z
      | .X => Sum.inl .X)
    invFun := (fun fv => match fv with
      | .inl _    => .X
      | .inr .y   => .y
      | .inr .z   => .z)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_X_xyX (phi : L.Formula Vars2xyX) : L.Formula (Vars1X ⊕ Vars2xy) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .y => Sum.inr .y
      | .x => Sum.inr .x
      | .X => Sum.inl .X)
    invFun := (fun fv => match fv with
      | .inl _    => .X
      | .inr .y   => .y
      | .inr .x   => .x)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_z_yzX (phi : L.Formula Vars2yzX) : L.Formula (Vars1z ⊕ Vars2yX) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .y => Sum.inr .y
      | .z => Sum.inl .z
      | .X => Sum.inr .X)
    invFun := (fun fv => match fv with
      | .inl _    => .z
      | .inr .y   => .y
      | .inr .X   => .X)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

@[delta0_simps]
def display_X_yX (phi : L.Formula Vars2yX) : L.Formula (Vars1X ⊕ Vars1y) :=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .y => Sum.inr .y
      | .X => Sum.inl .X)
    invFun := (fun fv => match fv with
      | .inl _    => .X
      | .inr .y   => .y)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
  }
-- END


@[delta0_simps]
def flip (phi : L.Formula (α ⊕ β)) : L.Formula (β ⊕ α) :=
  phi.relabelEquiv {
    toFun := Sum.swap (α := α) (β := β)
    invFun := Sum.swap
    left_inv := Sum.swap_leftInverse
    right_inv := Sum.swap_rightInverse
  }

@[delta0_simps]
def mkInl (phi : L.Formula α) : L.Formula (α ⊕ Empty) :=
  phi.relabelEquiv {
    toFun := Sum.inl
    invFun := Sum.elim id Empty.elim
    left_inv := by
      intro x
      simp only [Sum.elim_inl, id_eq]
    right_inv := by
      intro x
      cases x with
      | inl x => simp only [Sum.elim_inl, id_eq]
      | inr x => apply Empty.elim x
  }

end BoundedFormula

end FirstOrder.Language
