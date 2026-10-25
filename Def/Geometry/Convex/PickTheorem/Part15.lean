/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.ZMultiples
import Theorem.Geometry.Convex.PickTheorem.Part16
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

noncomputable def pickNormal (a c : Fin 2 → ℝ) :
    StrongDual ℝ (Fin 2 → ℝ) :=
  (c 0 - a 0) • ContinuousLinearMap.proj 1 -
    (c 1 - a 1) • ContinuousLinearMap.proj 0

noncomputable def pickSide (a c x : Fin 2 → ℝ) : ℝ :=
  pickNormal a c x - pickNormal a c a

noncomputable def pickHalfPlus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Ici (pickNormal a c a)

noncomputable def pickHalfMinus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Iic (pickNormal a c a)

end MetaMathlibExt
