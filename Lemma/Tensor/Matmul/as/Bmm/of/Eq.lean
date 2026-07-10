import Lemma.Tensor.Matmul.as.Bmm
open Tensor


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s = s')
  (X : Tensor α (s ++ [m, k]))
  (Y : Tensor α (s' ++ [k, n])) :
-- imply
  X.matmul Y (by grind) ≃ (cast (congrArg (Tensor α) (by grind)) X : Tensor α (s' ++ [m, k])).bmm Y := by
-- proof
  subst h_s
  apply Matmul.as.Bmm


-- created on 2026-07-10
