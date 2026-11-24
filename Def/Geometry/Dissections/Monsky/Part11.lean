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
public import Theorem.Geometry.Dissections.Monsky.Part10


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

noncomputable def monskyAtomWeight (V : ValuationSubring ℝ) :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → ZMod 2 :=
  Sym2.lift ⟨fun a b ↦ monskyEdgeWeight (monskyColor V a) (monskyColor V b), by
    intro a b
    exact monsky_edgeWeight_comm _ _⟩

end MetaMathlibExt
