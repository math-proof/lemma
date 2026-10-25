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
import Def.Geometry.Dissections.Monsky.Part5
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_faceParamList_sorted
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceParamList T htriangle f).SortedLT := by
  let l := (monskyFaceInteriorParams T htriangle f).sort (fun a b ↦ a ≤ b)
  have hl : l.SortedLT := Finset.sortedLT_sort _
  have hmem : ∀ r ∈ l, r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
      ((Finset.mem_sort _).1 hr)).1
  change ((0 :: l) ++ [1]).SortedLT
  rw [List.sortedLT_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.sortedLT_cons]
    exact ⟨fun r hr ↦ (hmem r hr).1, hl⟩
  · rw [List.sortedLT_iff_pairwise]
    exact List.pairwise_singleton (· < ·) 1
  · intro r hr q hq
    have hq1 : q = 1 := List.mem_singleton.mp hq
    subst q
    rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · exact (hmem r hr).2

end MetaMathlibExt
