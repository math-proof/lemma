import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Def.Data.Holor.Defs.Part4
import Notation.Data.Holor.Permute
open List Tensor


@[path]
private lemma main
-- given
  (h : s.length > d)
  (X : Tensor α s) :
-- imply
  (X.permuteTail d).length = s[0] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetAppend.eq.Get.of.GtLength]
    ·
      rw [GetTake.eq.Get.of.GtLengthTake]
    ·
      simpa
  ·
    simp
    omega


-- created on 2025-12-02
