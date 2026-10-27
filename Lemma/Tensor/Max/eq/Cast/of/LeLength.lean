import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Prod
import Theorem.Data.Holor.Functions
open List


@[path]
private lemma main
  [NeZero s.prod]
  [LT α] [DecidableLT α]
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.max d = cast (congrArg (Tensor α) (EqEraseIdx.of.LeLength h).symm) X := by
-- proof
  unfold Tensor.max Tensor.aminmax
  split_ifs with h_0
  ·
    omega
  ·
    rfl


-- created on 2025-12-04
