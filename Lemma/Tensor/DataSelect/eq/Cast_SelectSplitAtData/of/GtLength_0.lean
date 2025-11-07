import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.Lt_LengthSplitAtData.of.GtLength_0
import sympy.tensor.tensor
open Bool Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h_d⟩ i).data = cast (by sorry) (X.data.splitAt (d + 1))[i::(s.take d).prod] := by
-- proof
  sorry
  -- apply Eq_Cast.of.SEq
  -- apply DataGet.as.GetSplitAtData.of.GtLength_0 h


-- created on 2025-11-07
