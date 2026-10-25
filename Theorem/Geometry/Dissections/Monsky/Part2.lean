/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.BetweenList
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Side
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part3
import Lemma.Measure.Lebesgue.TriangleArea
import Def.Geometry.Dissections.Monsky
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_vertices_spec
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    t.1 = convexHull ℝ (Set.range (monskyVertices T htriangle t)) :=
  Classical.choose_spec (monsky_exists_vertices T htriangle t)

lemma monsky_vertices_independent
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineIndependent ℝ (monskyVertices T htriangle t) := by
  let p := monskyVertices T htriangle t
  have hp : t.1 = convexHull ℝ (Set.range p) := monsky_vertices_spec T htriangle t
  have hrange : Set.range p = {p 0, p 1, p 2} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hv := hvolume t.1 t.2
  rw [hp, hrange, MeasureTheory.toReal_volume_convexHull_triangle] at hv
  have hcyclic :
      (p 1 - p 0).ofLp 0 * (p 2 - p 0).ofLp 1 -
          (p 1 - p 0).ofLp 1 * (p 2 - p 0).ofLp 0 =
        (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
          (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 := by
    simp only [PiLp.sub_apply]
    ring
  have hdet : (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
      (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 ≠ 0 := by
    intro hzero
    rw [hcyclic, hzero, abs_zero, zero_div] at hv
    have hpos : (0 : ℝ) < 1 / (T.card : ℝ) := by
      positivity
    linarith
  have hi := monsky_affineIndependent_of_det_ne_zero (p 0) (p 1) (p 2) hdet
  have hpvec : ![p 0, p 1, p 2] = p := by
    funext i
    fin_cases i <;> rfl
  rw [hpvec] at hi
  exact hi

end MetaMathlibExt
