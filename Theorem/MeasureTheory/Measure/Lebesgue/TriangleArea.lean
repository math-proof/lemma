/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Notation.MeasureTheory.Measure.Lebesgue.TriangleArea
/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma mem_standardTriangle_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ convexHull ℝ
        ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2))) ↔
      0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
        0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 +
            ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1 := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | 0 ≤ ((euclideanPlaneBasis).toBasis.repr y) 0 ∧
      0 ≤ ((euclideanPlaneBasis).toBasis.repr y) 1 ∧
      ((euclideanPlaneBasis).toBasis.repr y) 0 +
        ((euclideanPlaneBasis).toBasis.repr y) 1 ≤ 1}
  have hconv : Convex ℝ S := by
    rw [convex_iff_add_mem]
    rintro y ⟨hy0, hy1, hys⟩ z ⟨hz0, hz1, hzs⟩ a b ha hb hab
    simp only [S, Set.mem_ofPred_eq, map_add, map_smul, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · positivity
    constructor
    · positivity
    · nlinarith
  constructor
  · intro hx
    change x ∈ S
    exact (convexHull_min (s :=
      ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2))))
      (t := S) (by rintro y (rfl | rfl | rfl) <;> simp [S]) hconv) hx
  · rintro ⟨hx0, hx1, hxsum⟩
    let r := ((euclideanPlaneBasis).toBasis.repr x) 0
    let s := ((euclideanPlaneBasis).toBasis.repr x) 1
    change 0 ≤ r at hx0
    change 0 ≤ s at hx1
    change r + s ≤ 1 at hxsum
    let w : Fin 3 → ℝ := ![1 - r - s, r, s]
    let z : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![0, euclideanPlaneBasis 0, euclideanPlaneBasis 1]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · simp [w, Fin.sum_univ_three]
      ring
    · intro i
      fin_cases i <;> simp [z]
    · have hrepr := (euclideanPlaneBasis).toBasis.sum_repr x
      rw [Fin.sum_univ_two] at hrepr
      simpa [w, z, r, s, Fin.sum_univ_three] using hrepr

end MetaMathlibExt
