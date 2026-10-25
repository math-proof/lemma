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
import Def.Geometry.Convex.PickTheorem.Part2
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


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
