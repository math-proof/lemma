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
public import Theorem.Geometry.Dissections.Monsky


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

noncomputable def monskyVertices
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  Classical.choose (monsky_exists_vertices T htriangle t)

end MetaMathlibExt
