import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Set.In_Iic.is.Le
open Set Nat


@[main]
private lemma main
  [Preorder α]
  {x y z : α}
-- given
  (hz : z ∈ Iic y)
  (hxy : x ≥ y) :
-- imply
  x ≥ z := by
-- proof
  apply Ge.of.Ge.Ge hxy
  exact ge_iff_le.mpr (Le.of.In_Iic hz)


-- created on 2018-07-01
