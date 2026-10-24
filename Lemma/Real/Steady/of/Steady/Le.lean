import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Real
open Real.Steady


/--
[Real.Steady.mono](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: Chapter6.Sequence}
  {ε₁ ε₂: ℝ}
-- given
  (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.Steady a) :
-- imply
  ε₂.Steady a :=
-- proof
  Real.Steady.mono hε hsteady


-- created on 2026-10-22
