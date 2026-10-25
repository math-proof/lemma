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
import Theorem.Geometry.Dissections.Monsky.Part3
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable def monskyFaceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ
    ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
      Set (EuclideanSpace ℝ (Fin 2)))

noncomputable def monskyIntersectionPoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T) :
    EuclideanSpace ℝ (Fin 2) := by
  classical
  exact if h : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
      monskyFaceLine T htriangle g).Nonempty then Classical.choose h
    else monskyFaceLeft T htriangle f

noncomputable def monskyNodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (EuclideanSpace ℝ (Fin 2)) := by
  classical
  exact
    (Finset.univ.image (monskyFaceLeft T htriangle) ∪
      Finset.univ.image (monskyFaceRight T htriangle)) ∪
      Finset.univ.biUnion fun f : MonskyFace T ↦
        Finset.univ.image fun g : MonskyFace T ↦ monskyIntersectionPoint T htriangle f g

noncomputable def monskyFaceInteriorParams
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) : Finset ℝ := by
  classical
  exact ((monskyNodes T htriangle).filter fun x ↦
      x ∈ openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)).image
    (Function.invFun (AffineMap.lineMap
      (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)))

end MetaMathlibExt
