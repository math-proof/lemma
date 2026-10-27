import Def.Data.Holor.BandPart
import Def.Data.Holor.Defs.Part4


@[path]
private lemma main
  [Zero α]
-- given
  (h : s.length < 2)
  (X : Tensor α s)
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool) :
-- imply
  X.masked_fill d cmp = X := by
-- proof
  unfold Tensor.masked_fill
  simp
  split_ifs
  repeat grind


-- created on 2026-07-29
