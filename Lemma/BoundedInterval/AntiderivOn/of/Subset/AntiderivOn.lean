import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_9.Part3
open Chapter9 Chapter10 Chapter11.BoundedInterval
open Chapter11
open Chapter11.AntiderivOn


/--
[AntiderivOn.mono](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_9.lean)
-/
@[path]
private lemma main
  {F f: ℝ → ℝ}
  {I J: BoundedInterval}
-- given
  (h: AntiderivOn F f I)
  (hIJ: J ⊆ I) :
-- imply
  AntiderivOn F f J :=
-- proof
  Chapter11.AntiderivOn.mono h hIJ


-- created on 2026-10-22
