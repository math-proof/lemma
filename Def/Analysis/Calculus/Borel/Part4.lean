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
public import Theorem.Analysis.Calculus.Borel.Part3

@[expose] public section

/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

/-- The `m`-th summand: `(aₘ/m!)·xᵐ·bump(x/rₘ)`. -/
noncomputable def g (a : ℕ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => coeff a m * x ^ m * bump ((radius a m)⁻¹ * x)

end Real.Calculus.Borel
