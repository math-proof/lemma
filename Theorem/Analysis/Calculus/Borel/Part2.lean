/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Borel.Part2
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma polyBound_nonneg (m : ℕ) : 0 ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).1

lemma norm_iteratedFDeriv_poly_le {m i : ℕ} (hi : i ≤ m) (y : ℝ) :
    ‖iteratedFDeriv ℝ i (poly m) y‖ ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).2 i hi y

end Real.Calculus.Borel
