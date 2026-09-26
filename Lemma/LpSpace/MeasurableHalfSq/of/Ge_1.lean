import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Lemma.LpSpace.ContinuousHalfSq.of.Ge_1
open LpSpace


@[main]
private lemma main
  {p d : ℕ}
-- given
  (h : 1 ≤ p) :
-- imply
  Measurable (half_sq : LpSpace p d → ℝ) := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast h⟩
  exact (ContinuousHalfSq.of.Ge_1 h).measurable


-- created on 2026-09-26