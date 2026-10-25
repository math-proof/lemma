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
import Def.Geometry.Convex.PickTheorem.Part5
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_mem_triangle_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) :
    x ∈ pickTriangle u v h ↔
      0 ≤ (pickBasis u v h).repr x 0 ∧
        0 ≤ (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 ≤ 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).convexHull_eq_nonneg_coord]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumle⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

theorem pick_mem_interior_triangle_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ interior (pickTriangle u v h) ↔
      0 < (pickBasis u v h).repr x 0 ∧
        0 < (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 < 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).interior_convexHull]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumlt⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

end MetaMathlibExt
