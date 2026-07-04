import Lemma.Tensor.LengthPermute.eq.Length.of.GtVal_0
open Tensor


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h_i : i.val > 0)
  (h_d : d ≥ 0)
  (X : Tensor α s) :
-- imply
  (X.permute i d).length = X.length := by
-- proof
  have := LengthPermute.eq.Length.of.GtVal_0 h_i X d.toNat
  rwa [Int.EqToNat.of.Ge_0] at this
  assumption


-- created on 2026-07-04
