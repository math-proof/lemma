import Lemma.Tensor.GetOfVector.eq.Get
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.LengthMaskedFill.eq.Length
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapMaskedFill.eq.MaskedFillMap.of.GtLength_2 |
| comm | Tensor.MaskedFillMap.eq.MapMaskedFill.of.GtLength_2 |
-/
@[main, fin, comm, fin.comm]
private lemma main
  [Zero α]
-- given
  (h : s.length > 2)
  (X : Tensor α s)
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool)
  (i : Fin s[0]) :
-- imply
  (X.masked_fill d cmp)[i]'(by rw [LengthMaskedFill.eq.Length]; apply GtLength.of.GtLength_0 (by grind)) = (X[i]'(GtLength.of.GtLength_0 (by grind) X i)).masked_fill d cmp := by
-- proof
  match s with
  | [] =>
    grind
  | n :: s =>
    rw [Tensor.masked_fill, dif_pos h]
    simp [GetElem.getElem]
    erw [GetOfVector.eq.Get.fin]
    simp
    congr 1


-- created on 2026-07-29
