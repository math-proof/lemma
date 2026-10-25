/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Series/NormalConvergence.lean -/


import Def.Analysis.Normed.Series.NormalConvergence
import Lemma.Real.NormalConvergence
import Mathlib.Analysis.Normed.Field.Basic
import Theorem.MathlibExtTest.Analysis.Normed.Series.NormalConvergence
open Topology
open scoped ENNReal

/-!
# Tests for normal convergence of series of functions

Exercises `supNormOn`, `ConvergesNormallyOn`, and
`ConvergesLocallyNormallyOn`: the empty-set and zero-series simp lemmas,
monotonicity under shrinking the domain, projection from local convergence
at a point, and a concrete nonzero one-term series on a singleton domain.
-/


/-- A concrete one-term series on `ℝ`: only the `n = 0` term is nonzero. -/
def oneTermSeries : ℕ → ℝ → ℝ := fun n _ => if n = 0 then 1 else 0

