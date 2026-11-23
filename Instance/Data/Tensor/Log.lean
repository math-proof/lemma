module

public import Instance.Data.Tensor.Tensor.Part2
public import Instance.Data.Vector.Functions
public import Instance.Analysis.SpecialFunctions.Logarithm
@[expose] public section

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

