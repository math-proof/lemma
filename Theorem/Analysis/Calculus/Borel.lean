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
import Def.Analysis.Calculus.Borel
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma contDiff_poly (m : ℕ) : ContDiff ℝ ∞ (poly m) := by
  unfold poly
  exact (contDiff_id.pow m).mul bump.contDiff

lemma hasCompactSupport_poly (m : ℕ) : HasCompactSupport (poly m) := by
  unfold poly
  exact bump.hasCompactSupport.mul_left

end Real.Calculus.Borel
