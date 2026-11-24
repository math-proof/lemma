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
public import Theorem.Geometry.Dissections.Monsky.Part6


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

/-- The mod-two edge weight used in the Sperner count.  It detects an edge whose endpoint
colours are `0` and `2`. -/
def monskyEdgeWeight (i j : Fin 3) : ZMod 2 :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0

def monskyPathWeight : List (Fin 3) → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => monskyEdgeWeight a b + monskyPathWeight (b :: l)

end MetaMathlibExt
