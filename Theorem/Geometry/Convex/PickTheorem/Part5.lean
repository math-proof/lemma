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
public import Def.Geometry.Convex.PickTheorem.Part4


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

theorem pick_affineBasis_basisOf_zero (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    ((pickAffineBasis u v h).basisOf 0).reindex
        (finSuccAboveEquiv (0 : Fin 3)).symm = pickBasis u v h := by
  ext i x
  fin_cases i <;>
    simp [Module.Basis.reindex_apply, pickTrianglePoints, finSuccAboveEquiv_apply,
      pick_basis_apply, pickVecs, pickCast]

theorem pick_affineBasis_coord_succ (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) (x : Fin 2 → ℝ) :
    (pickAffineBasis u v h).coord (Fin.succ i) x = (pickBasis u v h).repr x i := by
  let e := finSuccAboveEquiv (0 : Fin 3)
  have he : (e i : Fin 3) = Fin.succ i := by simp [e, finSuccAboveEquiv_apply]
  rw [← he]
  calc
    (pickAffineBasis u v h).coord (e i) x =
        ((pickAffineBasis u v h).basisOf 0).repr x (e i) :=
      pick_coord_eq_basisOf_repr _ (by simp [pickTrianglePoints]) (e i) x
    _ = (((pickAffineBasis u v h).basisOf 0).reindex e.symm).repr x i := by
      simp [Module.Basis.repr_reindex]
    _ = (pickBasis u v h).repr x i := by rw [pick_affineBasis_basisOf_zero]

end MetaMathlibExt
