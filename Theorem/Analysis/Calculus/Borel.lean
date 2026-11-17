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
public import Def.Analysis.Calculus.Borel

/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/

public section


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma contDiff_poly (m : ℕ) : ContDiff ℝ ∞ (poly m) := by
  unfold poly
  exact (contDiff_id.pow m).mul bump.contDiff

lemma hasCompactSupport_poly (m : ℕ) : HasCompactSupport (poly m) := by
  unfold poly
  exact bump.hasCompactSupport.mul_left

end Real.Calculus.Borel
