import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
open LowerUnsignedLebesgueIntegral


/--
[LowerUnsignedLebesgueIntegral.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_3.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedMeasurable f)
  (hg: UnsignedMeasurable g)
  (hfg: UnsignedMeasurable (f + g)) :
-- imply
  LowerUnsignedLebesgueIntegral (f + g) = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g :=
-- proof
  LowerUnsignedLebesgueIntegral.add hf hg hfg


-- created on 2026-10-22
