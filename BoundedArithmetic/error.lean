-- Discussion of the problem: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/How.20can.20it.20throw.20an.20.60unknown.20identifier.60.3F/near/538625142

universe u

variable {num str: Type u}
variable [Zero num] [One num] [Add num] [LE num]
variable (seq : num -> str -> num)

structure VTC0 where
  b3  : ∀ x : num, x + 0 = x
  seq_ax : ∀ (x : num) (Z : str) (y : num),
    y = seq x Z ↔ True

variable (h : VTC0 seq)
#check h
#check VTC0.b3 h
#check h.b3

theorem leq_refl : ∀ x : num, x <= x := by
  intro x
  apply h -- here, unknown identifier 'h'
