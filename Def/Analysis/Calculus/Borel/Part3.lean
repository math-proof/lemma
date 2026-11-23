/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Theorem.Analysis.Calculus.Borel.Part2

@[expose] public section

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
