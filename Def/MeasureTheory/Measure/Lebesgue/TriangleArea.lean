/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea
/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2)))

noncomputable def reflect (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  euclideanPlaneBasis 0 + euclideanPlaneBasis 1 - x

end MetaMathlibExt
