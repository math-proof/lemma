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
public import Theorem.Analysis.Calculus.Borel.Part4

@[expose] public section

/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

/-- A uniform bound for the `k`-th derivative of `g a m`, from compact support. -/
noncomputable def gBound (a : ℕ → ℝ) (m k : ℕ) : ℝ :=
  Classical.choose ((g_hasCompactSupport a m).exists_bound_iteratedFDeriv (g_contDiff a m) k)

end Real.Calculus.Borel
