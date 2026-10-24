import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexContentChoiceBound
open StatMech StatMech.Universality


/--
[finiteChoice_sum_le_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentChoiceBound.lean)
-/
@[path]
private lemma finiteChoice_sum_le_prod_eq
  [DecidableEq ι]
  {active : Finset ι}
  {choices : ι → Finset κ}
  {objects : Finset β}
  {objectWeight : β → ℝ}
-- given
  (encode : β → ∀ i, i ∈ active → κ)
  (hencode : ∀ b ∈ objects, encode b ∈ active.pi choices)
  (hinjective : Set.InjOn encode (objects : Set β))
  (choiceWeight : ∀ i, κ → ℝ)
  (hweight : ∀ b ∈ objects, objectWeight b = ∏ i ∈ active.attach, choiceWeight i.1 (encode b i.1 i.2))
  (hnonneg : ∀ p ∈ active.pi choices, 0 ≤ ∏ i ∈ active.attach, choiceWeight i.1 (p i.1 i.2)) :
-- imply
  ∑ b ∈ objects, objectWeight b ≤ ∏ i ∈ active, ∑ k ∈ choices i, choiceWeight i k := by
-- proof
  apply StatMech.Universality.finiteChoice_sum_le_prod active choices objects encode hencode hinjective choiceWeight objectWeight hweight hnonneg


-- created on 2026-10-23
