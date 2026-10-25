import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open Filter
open ENNReal


/--
[ENNReal.tsum_of_tsum'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {x: ℕ → ℕ → ENNReal} :
-- imply
  ∑' p:ℕ × ℕ, x p.1 p.2 = ∑' m, ∑' n, x n m :=
-- proof
  ENNReal.tsum_of_tsum' x


-- created on 2026-10-22
