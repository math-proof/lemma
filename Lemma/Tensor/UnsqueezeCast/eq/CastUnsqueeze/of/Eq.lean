import sympy.tensor.Basic
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Unsqueeze.as.UnsqueezeCast.of.Eq
open Bool Tensor


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_s : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).unsqueeze d = cast (by simp [h_s]) (X.unsqueeze d) := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEq.symm
  apply Unsqueeze.as.UnsqueezeCast.of.Eq h_s


-- created on 2025-10-10
