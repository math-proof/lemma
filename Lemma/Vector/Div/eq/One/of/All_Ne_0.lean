import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGet1_1
import Lemma.Vector.GetDiv.eq.DivGetS
import sympy.vector.vector
open Vector


@[main]
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


@[main]
private lemma fin
  [GroupWithZero α]
  {x : List.Vector α n}
-- given
  (h : ∀ i : Fin n, x.get i ≠ 0) :
-- imply
  x / x = 1 :=
-- proof
  main h


-- created on 2025-11-28
