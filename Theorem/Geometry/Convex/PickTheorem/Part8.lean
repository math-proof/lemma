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
import Def.Geometry.Convex.PickTheorem.Part7
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_triangle_inter_reflect_subset_diagonal (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h) ⊆ pickDiagonal u v h := by
  rintro x ⟨hx, hrx⟩
  obtain ⟨-, -, hle⟩ := (pick_mem_triangle_iff u v h x).1 hx
  obtain ⟨-, -, hge⟩ := (pick_mem_reflected_triangle_iff u v h x).1 hrx
  exact (pick_mem_diagonal_iff u v h x).2 (le_antisymm hle hge)

theorem pick_volume_triangle_inter_reflect (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h)) = 0 := by
  exact MeasureTheory.measure_mono_null (pick_triangle_inter_reflect_subset_diagonal u v h)
    (volume.addHaar_affineSubspace (pickDiagonal u v h) (pick_diagonal_ne_top u v h))

theorem pick_two_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
      ENNReal.ofReal |(pickDet u v : ℝ)| := by
  calc
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
        volume (pickTriangle u v h) +
          volume (pickReflect u v h '' pickTriangle u v h) := by
      rw [pick_volume_reflected_triangle]
    _ = volume (pickTriangle u v h ∪ pickReflect u v h '' pickTriangle u v h) := by
      have hunion := measure_union_add_inter (μ := volume) (pickTriangle u v h)
        (pick_reflected_triangle_measurableSet u v h)
      rw [pick_volume_triangle_inter_reflect, add_zero] at hunion
      exact hunion.symm
    _ = volume (parallelepiped (pickBasis u v h)) := by
      rw [pick_parallelepiped_eq_union]
    _ = volume (ZSpan.fundamentalDomain (pickBasis u v h)) := by
      exact (ZSpan.fundamentalDomain_ae_parallelepiped (pickBasis u v h) volume).measure_eq.symm
    _ = ENNReal.ofReal |(pickDet u v : ℝ)| := by
      rw [ZSpan.volume_fundamentalDomain, pick_matrix_of_basis, pick_matrix_det]

theorem pick_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (volume (pickTriangle u v h)).toReal = |(pickDet u v : ℝ)| / 2 := by
  have hfinite : volume (pickTriangle u v h) ≠ ⊤ :=
    ne_of_lt (pick_triangle_isCompact u v h).measure_lt_top
  have hre := congrArg ENNReal.toReal (pick_two_volume_triangle u v h)
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal (abs_nonneg _)] at hre
  linarith

end MetaMathlibExt
