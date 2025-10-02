import sympy.tensor.tensor
import sympy.vector.vector.functions
open Tensor

/--
[exp](https://pytorch.org/docs/stable/generated/torch.exp.html)
-/
instance [Exp α] : Exp (Tensor α s) where
  exp X := ⟨Exp.exp X.data⟩
  exp_add x y := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataMul.eq.MulDataS]
    apply Exp.exp_add

/--
[log](https://pytorch.org/docs/stable/generated/torch.log.html)
-/
instance [Log α] : Log (Tensor α s) where
  log X := ⟨Log.log X.data⟩
