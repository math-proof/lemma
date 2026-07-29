import Lemma.Tensor.MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapTriu.eq.TriuMap.of.EqUFn0'0 |
| comm | Tensor.TriuMap.eq.MapTriu.of.EqUFn0'0 |
-/
@[main, comm]
private lemma main
  [Zero α]
  [Zero β]
  {f : α → β}
-- given
  (hf : f 0 = 0)
  (X : Tensor α s)
  (d : ℤ) :
-- imply
  (X.triu d).map f = (X.map f).triu d := by
-- proof
  unfold Tensor.triu
  rw [MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0 hf]


-- created on 2026-07-29
