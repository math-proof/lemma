/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Series/NormalConvergence.lean -/


import Def.Analysis.Normed.Series.NormalConvergence
import Lemma.Real.NormalConvergence
import Mathlib.Analysis.Normed.Field.Basic
import Def.MathlibExtTest.Analysis.Normed.Series.NormalConvergence
open Topology
open scoped ENNReal

/-!
# Tests for normal convergence of series of functions

Exercises `supNormOn`, `ConvergesNormallyOn`, and
`ConvergesLocallyNormallyOn`: the empty-set and zero-series simp lemmas,
monotonicity under shrinking the domain, projection from local convergence
at a point, and a concrete nonzero one-term series on a singleton domain.
-/


/-- The active term is genuinely nonzero on the singleton domain. -/
example : supNormOn (oneTermSeries 0) ({0} : Set ℝ) = 1 := by
  rw [supNormOn_oneTermSeries, ite_eq_left rfl]

/-- The one-term series converges locally normally on the singleton `{0}`. -/
example : ConvergesLocallyNormallyOn oneTermSeries ({0} : Set ℝ) := by
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp [oneTermSeries_normal]⟩

