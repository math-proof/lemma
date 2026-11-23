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
public import Theorem.Geometry.Convex.PickTheorem.Part2

@[expose] public section

/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

noncomputable def pickBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  let A := (pickMatrix u v).transpose
  let e : (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ :=
    Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) A <| by
      rw [isUnit_iff_ne_zero, Matrix.det_transpose, pick_matrix_det]
      exact_mod_cast h
  (Pi.basisFun ℝ (Fin 2)).map e

end MetaMathlibExt
