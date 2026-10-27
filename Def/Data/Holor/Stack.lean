import Instance.Data.Holor.Tensor.Part2
open Lean


/--
[stack](https://docs.pytorch.org/docs/stable/generated/torch.stack.html)
-/
def Stack (n : ℕ) (f : Fin n → Tensor α shape) : Tensor α (n :: shape) :=
  Tensor.OfVector ((List.Vector.range n).map f)


