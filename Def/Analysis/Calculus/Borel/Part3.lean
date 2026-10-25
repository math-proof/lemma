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
import Theorem.Analysis.Calculus.Borel.Part2
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

/-- The `m`-th Taylor coefficient we want to realize, `aₘ / m!`. -/
noncomputable def coeff (a : ℕ → ℝ) (m : ℕ) : ℝ := a m / (Nat.factorial m : ℝ)

/-- The radius of the `m`-th cutoff, chosen small enough to control the derivatives. -/
noncomputable def radius (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  min 1 ((1 / 2) ^ m / (|coeff a m| * polyBound m + 1))

end Real.Calculus.Borel
