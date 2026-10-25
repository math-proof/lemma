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
import Def.Geometry.Convex.PickTheorem.Part15
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_lattice_segment_ncard {A C : Fin 2 → ℤ} (hAC : A ≠ C) :
    (pickLatticePoints (segment ℝ (pickCast A) (pickCast C))).ncard =
      (pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))).ncard + 2 := by
  let O := pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))
  have hset : pickLatticePoints (segment ℝ (pickCast A) (pickCast C)) = {A, C} ∪ O := by
    change pickCast ⁻¹' segment ℝ (pickCast A) (pickCast C) = {A, C} ∪ O
    dsimp only [O]
    rw [← insert_endpoints_openSegment ℝ]
    ext z
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [pick_cast_injective.eq_iff, pick_cast_injective.eq_iff]
    tauto
  have hdisj : Disjoint ({A, C} : Set (Fin 2 → ℤ)) O := by
    rw [Set.disjoint_left]
    intro z hz hzO
    rcases hz with hza | hzc
    · rw [hza] at hzO
      apply hAC
      apply pick_cast_injective
      exact left_mem_openSegment_iff.mp hzO
    · rw [Set.mem_singleton_iff] at hzc
      rw [hzc] at hzO
      apply hAC
      apply pick_cast_injective
      exact right_mem_openSegment_iff.mp hzO
  have hO : O.Finite := by
    have hpair : ({pickCast A, pickCast C} : Set (Fin 2 → ℝ)).Finite :=
      Set.finite_insert.mpr (Set.finite_singleton _)
    have hseg : IsCompact (segment ℝ (pickCast A) (pickCast C)) := by
      rw [← convexHull_pair]
      exact hpair.isCompact_convexHull ℝ
    apply (pick_lattice_preimage_finite hseg).subset
    intro z hz
    exact openSegment_subset_segment ℝ _ _ hz
  dsimp only [O] at hset hdisj hO ⊢
  rw [hset, Set.ncard_union_eq hdisj (Set.finite_insert.mpr (Set.finite_singleton C)) hO,
    Set.ncard_pair hAC]
  omega

end MetaMathlibExt
