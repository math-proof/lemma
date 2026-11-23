/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
public import Def.Geometry.Convex.PickTheorem.Part2

/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/

public section


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_basis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) (i : Fin 2) :
    pickBasis u v h i = pickVecs u v i := by
  rw [pickBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  ext j
  simp [pickMatrix, pickVecs, pickCast]

theorem pick_matrix_of_basis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Matrix.of (pickBasis u v h) = pickMatrix u v := by
  ext i j
  simp [pick_basis_apply, pickMatrix]

end MetaMathlibExt
