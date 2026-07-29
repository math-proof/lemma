import Lemma.Tensor.MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapTril.eq.TrilMap.of.EqUFn0'0 |
| comm | Tensor.TrilMap.eq.MapTril.of.EqUFn0'0 |
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
  (X.tril d).map f = (X.map f).tril d := by
-- proof
  unfold Tensor.tril
  rw [MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0 hf]


-- created on 2026-07-29
