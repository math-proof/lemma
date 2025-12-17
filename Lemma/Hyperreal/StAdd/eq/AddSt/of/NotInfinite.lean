import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (r : ℝ) :
-- imply
  (x + r).st = x.st + r := by
-- proof
  rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h]
  ·
    simp
    apply EqSt
  ·
    apply NotInfinite


-- created on 2025-12-11
-- updated on 2025-12-12
