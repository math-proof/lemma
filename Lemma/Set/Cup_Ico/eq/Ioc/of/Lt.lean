import Lemma.Set.Cup_Ioc.eq.Ioc.of.Lt.Ge_0
import Lemma.Set.Cup_Ioc.eq.Ioc.of.Lt.Lt_0
open Set


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ}
-- given
  (h : a < b) :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  if h_a : a ≥ 0 then
    apply Cup_Ioc.eq.Ioc.of.Lt.Ge_0 (R := R) h_a h
  else
    apply Cup_Ioc.eq.Ioc.of.Lt.Lt_0 (R := R) (Nat.Lt.of.NotGe h_a) h


-- created on 2018-10-16
