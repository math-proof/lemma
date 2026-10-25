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
import Theorem.Geometry.Dissections.Monsky.Part5
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable def monskyFacePointList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (EuclideanSpace ℝ (Fin 2)) :=
  (monskyFaceParamList T htriangle f).map
    (AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f))

noncomputable def monskyFaceAtomList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (Sym2 (EuclideanSpace ℝ (Fin 2))) :=
  (monskyFacePointList T htriangle f).consecutivePairs.map fun e ↦ s(e.1, e.2)

noncomputable def monskyAtoms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (Sym2 (EuclideanSpace ℝ (Fin 2))) := by
  classical
  exact Finset.univ.biUnion fun f : MonskyFace T ↦
    (monskyFaceAtomList T htriangle f).toFinset

noncomputable def monskyAtomMidpoint :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) :=
  Sym2.lift ⟨fun a b ↦ midpoint ℝ a b, fun a b ↦ midpoint_comm a b⟩

end MetaMathlibExt
