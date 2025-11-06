import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.Lt_Length.of.GtLength_0
open Tensor


@[main]
private lemma main
  {X Y : Tensor α s}
-- given
  (h_s : s.length > 0)
  (h : X = Y)
  (i : Fin s[0]) :
-- imply
  X.get ⟨i, by apply Lt_Length.of.GtLength_0 h_s⟩ = Y.get ⟨i, by apply Lt_Length.of.GtLength_0 h_s⟩ := by
-- proof
  apply All_EqGetS.of.Eq.GtLength_0 h_s h i


-- created on 2025-11-06
