import torch.Tensor.Basic
import Lemma.Nat.EqMulDiv.of.Dvd
open Tensor Nat

/--
[torch.reshape](https://docs.pytorch.org/docs/stable/generated/torch.reshape.html)
-/
def Tensor.reshape (X : Tensor α s) (s' : List ℕ) (h : s.prod ∣ s'.prod) : Tensor α s' :=
  ⟨cast (by rw [EqMulDiv.of.Dvd h]) (X.data.repeat (s'.prod / s.prod))⟩
