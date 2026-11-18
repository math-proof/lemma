module

public import Def.Data.Tensor.Defs.Part4
public import Def.Data.Vector.Basic.Part2
public import Theorem.Nat.EqMulDiv.of.Dvd

@[expose] public section
open Tensor Nat


/--
[torch.reshape](https://docs.pytorch.org/docs/stable/generated/torch.reshape.html)
-/
def Tensor.reshape (X : Tensor α s) (s' : List ℕ) (h : s.prod ∣ s'.prod) : Tensor α s' :=
  ⟨cast (by rw [EqMulDiv.of.Dvd h]) (X.data.repeat (s'.prod / s.prod))⟩

