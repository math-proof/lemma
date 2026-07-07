import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x → ∞)
  (r : ℝ) :
-- imply
  stdPart (x + r) = stdPart x + r := by
-- proof
  rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h]
  ·
    simp
  ·
    apply NotInfinite


-- created on 2025-12-11
-- updated on 2025-12-12
