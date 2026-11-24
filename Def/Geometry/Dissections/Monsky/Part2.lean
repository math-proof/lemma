module
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.BetweenList
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Side
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part3
public import Theorem.Measure.Lebesgue.TriangleArea
public import Theorem.Geometry.Dissections.Monsky.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/
namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable def monskyTriangleBasis
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
    ⟨monskyVertices T htriangle t, monsky_vertices_independent T htriangle hcard hvolume t⟩
  exact ⟨s.points, s.independent, s.affineSpan_eq_top (by simp)⟩

noncomputable def monskySquareCorner (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) :=
  ![0, euclideanPlaneBasis 0, euclideanPlaneBasis 0 + euclideanPlaneBasis 1,
    euclideanPlaneBasis 1] i

end MetaMathlibExt
