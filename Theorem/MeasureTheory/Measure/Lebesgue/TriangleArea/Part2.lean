/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Def.MeasureTheory.Measure.Lebesgue.TriangleArea
/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma repr_reflect (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    ((euclideanPlaneBasis).toBasis.repr (reflect x)) i =
      1 - ((euclideanPlaneBasis).toBasis.repr x) i := by
  fin_cases i <;> simp [reflect]

@[simp] lemma reflect_reflect (x : EuclideanSpace ℝ (Fin 2)) :
    reflect (reflect x) = x := by
  simp [reflect]

lemma mem_reflect_image_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ reflect '' standardTriangle ↔
      reflect x ∈ standardTriangle := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨reflect x, hx, reflect_reflect x⟩

lemma mem_reflectedTriangle_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ reflect '' standardTriangle ↔
      ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1 ∧
        ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1 ∧
          1 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 +
            ((euclideanPlaneBasis).toBasis.repr x) 1 := by
  rw [mem_reflect_image_iff, standardTriangle,
    mem_standardTriangle_iff, repr_reflect, repr_reflect]
  constructor <;> rintro ⟨h0, h1, hsum⟩ <;> constructor
  · linarith
  · constructor <;> linarith
  · linarith
  · constructor <;> linarith

lemma parallelepiped_eq_union :
    parallelepiped euclideanPlaneBasis =
      standardTriangle ∪ reflect '' standardTriangle := by
  rw [show parallelepiped euclideanPlaneBasis =
      parallelepiped (euclideanPlaneBasis).toBasis from rfl,
    parallelepiped_basis_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1 := hx 1
    rcases le_total (((euclideanPlaneBasis).toBasis.repr x) 0 +
      ((euclideanPlaneBasis).toBasis.repr x) 1) 1 with hsum | hsum
    · left
      rw [standardTriangle, mem_standardTriangle_iff]
      exact ⟨hx0.1, hx1.1, hsum⟩
    · right
      exact (mem_reflectedTriangle_iff x).2 ⟨hx0.2, hx1.2, hsum⟩
  · rintro (hx | hx) i
    · rw [standardTriangle, mem_standardTriangle_iff] at hx
      fin_cases i
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1
        exact ⟨hx.1, by linarith [hx.2.2]⟩
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1
        exact ⟨hx.2.1, by linarith [hx.2.2]⟩
    · rw [mem_reflectedTriangle_iff] at hx
      fin_cases i
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1
        exact ⟨by linarith [hx.2.2], hx.1⟩
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1
        exact ⟨by linarith [hx.2.2], hx.2.1⟩

end MetaMathlibExt
