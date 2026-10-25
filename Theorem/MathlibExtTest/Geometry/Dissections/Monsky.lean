/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Dissections/Monsky.lean -/


import Theorem.Geometry.Dissections.Monsky.Part11
import Lemma.Set.Dissections.Monsky
import Mathlib.Tactic


namespace MathlibExtTest.Geometry.Dissections.Monsky

open MeasureTheory

-- Three equal-area triangles cannot tile the unit square with disjoint interiors.
example (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))) (hcard : T.card = 3)
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c})
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (hcommon : ∃ A : ENNReal, ∀ t ∈ T, volume t = A) : False := by
  have heven := MetaMathlibExt.monsky_theorem T htriangle hcover hdisjoint hcommon
  rw [hcard] at heven
  norm_num at heven

end MathlibExtTest.Geometry.Dissections.Monsky
