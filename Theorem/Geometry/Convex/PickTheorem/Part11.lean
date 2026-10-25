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
import Def.Geometry.Convex.PickTheorem.Part10
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_sublattice_index (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickSublattice u v).index = (pickDet u v).natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) (pickSublattice u v)
    (pickSublatticeBasis u v h), Module.Basis.det_apply]
  have hmatrix :
      (Pi.basisFun ℤ (Fin 2)).toMatrix
          (fun i ↦ (pickSublatticeBasis u v h i : Fin 2 → ℤ)) =
        (pickIntMatrix u v).transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, pick_sublatticeBasis_apply, pickIntMatrix]
  rw [hmatrix, Matrix.det_transpose, pick_intMatrix_det]

theorem pick_repr_cast_intMap (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) :
    (pickBasis u v h).repr (pickCast (pickIntMap u v c)) i = (c i : ℝ) := by
  have hcast :
      pickCast (pickIntMap u v c) =
        (c 0 : ℝ) • pickBasis u v h 0 + (c 1 : ℝ) • pickBasis u v h 1 := by
    ext j
    fin_cases j <;>
      simp [pickIntMap, pickIntMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, pickCast, pick_basis_apply, pickVecs] <;> ring
  rw [hcast, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self]
  fin_cases i <;> simp

end MetaMathlibExt
