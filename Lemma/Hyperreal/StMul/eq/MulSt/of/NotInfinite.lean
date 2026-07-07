import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x → ∞)
  (r : ℝ) :
-- imply
  stdPart (x * r) = stdPart x * r := by
-- proof
  rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite h]
  ·
    simp
  ·
    apply NotInfinite


-- created on 2025-12-17
