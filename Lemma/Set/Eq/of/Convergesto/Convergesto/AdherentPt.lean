import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_3.Part2
open Chapter9
open Chapter9.Convergesto


/--
[Convergesto.uniq](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean)
-/
@[path]
private lemma main
  {E:Set ℝ}
  {f: ℝ → ℝ}
  {L L' x₀ : ℝ}
-- given
  (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀)
  (hf': Convergesto E f L' x₀) :
-- imply
  L = L' :=
-- proof
  Chapter9.Convergesto.uniq h hf hf'


-- created on 2026-10-22
