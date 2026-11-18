module

public import Def.Data.Tensor.Defs.Part3

@[expose] public section

/--
[stack](https://docs.pytorch.org/docs/stable/generated/torch.stack.html)
-/
def Stack (n : ℕ) (f : Fin n → Tensor α shape) : Tensor α (n :: shape) :=
  Tensor.OfVector ((List.Vector.range n).map f)
