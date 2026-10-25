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
import Abbrev.Geometry.Dissections.Monsky
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable def monskyFaceLeft
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 1)
  | .inr i => monskySquareCorner i

noncomputable def monskyFaceRight
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 2)
  | .inr i => monskySquareCorner (i + 1)

noncomputable def monskyCoordinate (i : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  (EuclideanSpace.projₗ i).toAffineMap

noncomputable def monskySquareSideForm (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  ![monskyCoordinate 1,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 0,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 1,
    monskyCoordinate 0] i

noncomputable def monskyFaceForm
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    MonskyFace T → EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ
  | .inl (t, i) => (monskyTriangleBasis T htriangle hcard hvolume t).coord i
  | .inr i => monskySquareSideForm i

end MetaMathlibExt
