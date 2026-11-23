/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part2

@[expose] public section

/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable def diagonal :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' (euclideanPlaneBasis 0)
    (LinearMap.ker (euclideanPlaneBasis).toBasis.sumCoords)

end MetaMathlibExt
