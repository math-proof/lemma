import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (r : ℝ) :
-- imply
  (x - r).st = x.st - r := by
-- proof
  have h := StAdd.eq.AddSt.of.NotInfinite h (-r)
  simp at h
  rw [← Sub.eq.Add_Neg] at h
  rw [h]
  rw [Sub.eq.Add_Neg]


-- created on 2025-12-21
