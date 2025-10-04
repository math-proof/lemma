import sympy.vector.vector
import sympy.functions.elementary.exponential
open Vector

namespace List.Vector

instance [Exp α] : Exp (Vector α n) where
  exp a := a.map Exp.exp
  exp_add x y := by
    ext i
    simp [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply Exp.exp_add
  exp_zero := by
    ext i
    simp [Zero.eq.Replicate]
    simp [One.eq.Replicate]
    apply Exp.exp_zero
  exp_neg x := by
    ext i
    simp [GetInv.eq.InvGet.fin]
    simp [GetNeg.eq.NegGet.fin]
    apply Exp.exp_neg

instance [NeZero n] [ExpNeZero α] : ExpNeZero (Vector α n) where
  exp_ne_zero x := by
    simp [Exp.exp]
    intro h_eq
    have h_head := EqGetS.of.Eq.fin h_eq ⟨0, NeZero.pos n⟩
    simp at h_head
    simp [Zero.eq.Replicate] at h_head
    simp [ExpNeZero.exp_ne_zero] at h_head


instance [Log α] : Log (Vector α n) where
  log a := a.map Log.log


def softmax [Div α] [Exp α] (x : Vector α n) : Vector α n :=
  let x_exp := exp x
  x_exp / x_exp.sum

end List.Vector
