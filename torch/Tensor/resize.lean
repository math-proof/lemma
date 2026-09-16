import torch.Tensor.Basic
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength

/-!
Methods on `Tensor` mirroring methods of the Python class `torch.Tensor`
(e.g. the in-place `torch.Tensor.resize_`).
-/

open List Tensor


/--
[numpy.resize](https://numpy.org/doc/stable/reference/generated/numpy.resize.html)
The closest PyTorch API is the `torch.Tensor` method
[`resize_`](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.resize_.html);
there is no top-level `torch.resize`.
-/
def Tensor.resize [Zero α] (X : Tensor α s) (dim : Fin s.length) (n : ℕ) : Tensor α (s.set dim n) :=
  ⟨cast (congrArg (List.Vector α) (MulProd_Mul_Prod.eq.ProdSet.of.GtLength dim.isLt n)) ((X.data.splitAt dim).map (·.resize (n * (s.drop dim.succ).prod))).flatten⟩
