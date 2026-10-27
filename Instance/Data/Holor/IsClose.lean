import Instance.Data.Holor.Tensor.Part2
import Instance.Data.Vector.Functions.Part2
import Theorem.Analysis.Real.Relational
open Tensor


/--
the approx operator that defines asymptotically equivalence/closeness between hyperreal numbers.
numerical analogy:
- [isclose](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.isclose.html)
-/
instance [XEq α] : XEq (Tensor α s) where
  r A B := A.data ≈ B.data
  iseqv :=
    {
      refl x := by simp
      symm {a b} h := h.symm
      trans {a b c} h_ab h_bc := h_ab.trans h_bc
    }

