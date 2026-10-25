import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Real
open Real.EventuallyClose


/--
[Real.EventuallyClose.mono](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: Chapter6.Sequence}
  {ε₁ ε₂ L: ℝ}
-- given
  (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
-- imply
  ε₂.EventuallyClose a L :=
-- proof
  Real.EventuallyClose.mono hε hclose


-- created on 2026-10-22
