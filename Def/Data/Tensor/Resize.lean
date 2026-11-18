module

public import Def.Data.Tensor.Defs.Part4
public import Def.Data.Vector.Basic.Part2
public import Theorem.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength

@[expose] public section
open List Tensor


/-!
Methods on `Tensor` mirroring methods of the Python class `torch.Tensor`
(e.g. the in-place `torch.Tensor.resize_`).
-/


/--
[numpy.resize](https://numpy.org/doc/stable/reference/generated/numpy.resize.html)
The closest PyTorch API is the `torch.Tensor` method
[`resize_`](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.resize_.html);
there is no top-level `torch.resize`.
-/
def Tensor.resize [Zero α] (X : Tensor α s) (dim : Fin s.length) (n : ℕ) : Tensor α (s.set dim n) :=
  ⟨cast (congrArg (List.Vector α) ((ProdSet.eq.MulProd_Mul_Prod.of.GtLength dim.isLt n).symm)) ((X.data.splitAt dim).map (·.resize (n * (s.drop dim.succ).prod))).flatten⟩

