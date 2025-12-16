import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StNeg.eq.NegSt
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_a : ¬Hyperreal.Infinite x)
  (h_b : ¬Hyperreal.Infinite y) :
-- imply
  (x - y).st = x.st - y.st := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_a]
  ·
    rw [StNeg.eq.NegSt]
    rw [Sub.eq.Add_Neg]
  ·
    rwa [InfiniteNeg.is.Infinite]


-- created on 2025-12-10
-- updated on 2025-12-16
