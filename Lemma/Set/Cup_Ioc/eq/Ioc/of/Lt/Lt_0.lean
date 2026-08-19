import Lemma.Set.Cup_Ioc.eq.Ioc.of.Lt_0.Ge_0
import Lemma.Set.Cup_Ioc.eq.Ioc.of.Lt.Lt_0.Lt_0
import Lemma.Nat.NotLt.is.Ge
open Set Nat


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ}
-- given
  (h_a : a < 0)
  (h_ab : a < b) :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  if h_b : b < 0 then
    apply Cup_Ioc.eq.Ioc.of.Lt.Lt_0.Lt_0 (R := R) h_a h_b h_ab
  else
    apply Cup_Ioc.eq.Ioc.of.Lt_0.Ge_0 (R := R) h_a (Ge.of.NotLt h_b)


-- created on 2018-10-15
