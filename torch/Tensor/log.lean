import torch.Tensor
import sympy.vector.functions
import sympy.functions.elementary.exponential
open Tensor

/--
[log](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.log.html)
-/
instance [Log α] : Log (Tensor α s) where
  log X := ⟨Log.log X.data⟩
  log_zero := by
    apply Eq.of.EqDataS
    apply Log.log_zero
  log_one := by
    apply Eq.of.EqDataS
    apply Log.log_one
  log_div_self x := by
    apply Eq.of.EqDataS
    rw [DataDiv.eq.DivDataS]
    rw [EqData0'0]
    apply Log.log_div_self
