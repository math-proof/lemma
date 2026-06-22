import Lemma.Tensor.DataSelect.as.FlattenGetSliceSplitAtData.of.GtLength
open Tensor


@[main, cast]
private lemma simp
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select d i).data ≃ (X.data.splitAt (d + 1))[i : (s.take (d + 1)).prod:s[d]].flatten := by
-- proof
  apply DataSelect.as.FlattenGetSliceSplitAtData.of.GtLength.simp


@[main, cast]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select d i).data ≃ (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  apply simp


-- created on 2026-06-22
