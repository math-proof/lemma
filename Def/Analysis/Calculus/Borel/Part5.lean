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
import Theorem.Analysis.Calculus.Borel.Part4
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

/-- A uniform bound for the `k`-th derivative of `g a m`, from compact support. -/
noncomputable def gBound (a : ℕ → ℝ) (m k : ℕ) : ℝ :=
  Classical.choose ((g_hasCompactSupport a m).exists_bound_iteratedFDeriv (g_contDiff a m) k)

end Real.Calculus.Borel
