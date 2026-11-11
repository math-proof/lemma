import Def.Data.Tensor.Defs.Part4
import Theorem.Data.Tensor.Functions


@[path]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim = cast (congrArg (Tensor α) (List.EqEraseIdx.of.LeLength h)) X := by
-- proof
  unfold Tensor.keepdim
  split_ifs with h_0
  .
    omega
  .
    rfl


-- created on 2025-12-04
