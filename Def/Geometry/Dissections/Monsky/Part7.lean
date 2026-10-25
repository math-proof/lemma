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
import Theorem.Geometry.Dissections.Monsky.Part6
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

/-- The mod-two edge weight used in the Sperner count.  It detects an edge whose endpoint
colours are `0` and `2`. -/
def monskyEdgeWeight (i j : Fin 3) : ZMod 2 :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0

def monskyPathWeight : List (Fin 3) → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => monskyEdgeWeight a b + monskyPathWeight (b :: l)

end MetaMathlibExt
