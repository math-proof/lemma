import Lemma.Vector.Eq.is.All_EqGetS
open Vector


@[path, fin 1]
private lemma main
  [GroupWithZero α]
  {x : List.Vector α n}
-- given
  (h : ∀ i : Fin n, x[i] ≠ 0) :
-- imply
  x / x = 1 := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGet1_1]
  rw [GetDiv.eq.DivGetS]
  rw [Rat.Div.eq.One.of.Ne_0]
  apply h i


-- created on 2025-11-28
