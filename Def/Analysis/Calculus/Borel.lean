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
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

/-- A fixed smooth bump function: equal to `1` on `[-1,1]`, supported in `(-2,2)`. -/
noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The polynomial `yᵐ` multiplied by the fixed bump. Smooth with compact support. -/
noncomputable def poly (m : ℕ) : ℝ → ℝ := fun y => y ^ m * bump y

end Real.Calculus.Borel
