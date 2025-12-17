import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Nat.Add
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (r : ℝ)
  (h : ¬x.Infinite) :
-- imply
  (r + x).st = r + x.st := by
-- proof
  rw [Add.comm]
  rw [StAdd.eq.AddSt.of.NotInfinite h]
  rw [Add.comm]


-- created on 2025-12-17
