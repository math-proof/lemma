import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
open Set Function OrientationTheorem


/--
[compact_subset_complement_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Lemma32_4.lean)
-/
@[path]
private lemma compact_subset_complement_eventually_eq
  [TopologicalSpace X]
  {A : ℕ → Set X}
  {K : Set X}
-- given
  (hA_closed : ∀ i, IsClosed (A i))
  (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
  (hK : IsCompact K)
  (hKA : K ⊆ (⋂ i, A i)ᶜ) :
-- imply
  ∃ i, K ⊆ (A i)ᶜ := by
-- proof
  apply OrientationTheorem.compact_subset_complement_eventually A hA_closed hA_decreasing K hK hKA


-- created on 2026-10-23
