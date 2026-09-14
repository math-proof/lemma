import sympy.tensor.Basic
open Tensor

/-!
Activation functions mirroring `torch.nn.functional`.
-/

/--
Scalar ReLU: `max x 0`.
[relu](https://pytorch.org/docs/stable/generated/torch.nn.functional.relu.html)
-/
def relu [Zero α] [Max α] (x : α) : α :=
  max x 0

/--
Elementwise ReLU over a tensor.
[relu](https://pytorch.org/docs/stable/generated/torch.nn.functional.relu.html)
-/
def Tensor.relu [Zero α] [Max α] (X : Tensor α s) : Tensor α s :=
  ⟨X.data.map fun x => max x 0⟩
