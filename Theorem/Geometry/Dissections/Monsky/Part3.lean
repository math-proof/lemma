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
import Def.Geometry.Dissections.Monsky.Part3
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_face_endpoints_ne
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : monskyFaceLeft T htriangle f ≠ monskyFaceRight T htriangle f := by
  rcases f with ⟨t, i⟩ | i
  · apply (monsky_vertices_independent T htriangle hcard hvolume t).injective.ne
    fin_omega
  · fin_cases i
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this

lemma monsky_mem_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ t.1 ↔ ∀ i : Fin 3, 0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.convexHull_eq_nonneg_coord]
  rfl

lemma monsky_mem_interior_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ interior t.1 ↔
      ∀ i : Fin 3, 0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.interior_convexHull]
  rfl

end MetaMathlibExt
