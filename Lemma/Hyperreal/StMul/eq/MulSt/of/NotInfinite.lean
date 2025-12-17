import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (r : ℝ) :
-- imply
  (x * r).st = x.st * r := by
-- proof
  rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite h]
  ·
    simp [EqSt]
  ·
    apply NotInfinite


-- created on 2025-12-17
