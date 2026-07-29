import Lemma.Tensor.MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0
import Lemma.Tensor.MapTril.eq.TrilMap.of.EqUFn0'0
import Lemma.Tensor.MapTriu.eq.TriuMap.of.EqUFn0'0
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapBandPart.eq.BandPartMap.of.EqUFn0'0 |
| comm | Tensor.BandPartMap.eq.MapBandPart.of.EqUFn0'0 |
-/
@[main, comm]
private lemma main
  [Zero α]
  [Zero β]
  {f : α → β}
-- given
  (hf : f 0 = 0)
  (X : Tensor α s)
  (l u d : ℕ) :
-- imply
  (X.band_part l u d).map f = (X.map f).band_part l u d := by
-- proof
  unfold Tensor.band_part
  rw [MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0 hf]
  congr 1
  rw [MapTriu.eq.TriuMap.of.EqUFn0'0 hf]
  congr 1
  rw [MapTril.eq.TrilMap.of.EqUFn0'0 hf]


-- created on 2026-07-29
