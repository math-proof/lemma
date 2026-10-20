import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Dissections.Monsky
open MeasureTheory Set
open MetaMathlibExt


/--
[monsky_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_theorem_eq
  :
-- imply
  ∀ (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
    (∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2), t = convexHull ℝ {a, b, c}) →
    Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
    {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} →
    (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior →
    (∃ A : ENNReal, ∀ t ∈ T, MeasureTheory.volume t = A) →
    Even T.card := by
-- proof
  apply MetaMathlibExt.monsky_theorem


-- created on 2026-10-20
