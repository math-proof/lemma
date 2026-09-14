import sympy.tensor.tensor
import sympy.vector.functions
import sympy.functions.elementary.exponential
open Tensor

/--
[exp](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.exp.html)
-/
instance [Exp α] : Exp (Tensor α s) where
  exp X := ⟨Exp.exp X.data⟩
  exp_add x y := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataMul.eq.MulDataS]
    apply Exp.exp_add
  exp_zero := by
    apply Eq.of.EqDataS
    apply Exp.exp_zero
  exp_neg x := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    rw [DataInv.eq.InvData]
    apply Exp.exp_neg

instance [NeZero s.prod] [ExpNeZero α] : ExpNeZero (Tensor α s) where
  exp_ne_zero x := by
    intro h_eq
    rw [Eq.is.EqDataS] at h_eq
    simp [EqData0'0] at h_eq
    have h := ExpNeZero.exp_ne_zero x.data
    contradiction
