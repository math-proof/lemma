import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import sympy.vector.lp_space
import sympy.Basic
open LpSpace


@[main]
private lemma main
  {p d : ℕ}
-- given
  (h : 1 ≤ p) :
-- imply
  Measurable (half_sq' : LpSpace p d → LpSpace p d) := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast h⟩
  unfold half_sq'
  refine Measurable.comp (WithLp.measurable_toLp _ _) (measurable_pi_iff.2 fun i => ?_)
  have hi : Measurable fun x : LpSpace p d => x i := (measurable_pi_apply i).comp (WithLp.measurable_ofLp _ _)
  have hn : Measurable fun x : LpSpace p d => ‖x‖ := continuous_norm.measurable
  exact ((hn.pow_const _).mul ((continuous_abs.measurable.comp hi).pow_const _)).mul hi


-- created on 2026-09-26