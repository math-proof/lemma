module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.ZMultiples
public import Def.Geometry.Convex.PickTheorem.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/
namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_trianglePoints_affineIndependent (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : AffineIndependent ℝ (pickTrianglePoints u v h) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
  let e := finSuccAboveEquiv (0 : Fin 3)
  have hli := (pickBasis u v h).linearIndependent.comp e.symm e.symm.injective
  convert hli using 1
  funext q
  rcases q with ⟨j, hj⟩
  fin_cases j
  · simp at hj
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl

end MetaMathlibExt
