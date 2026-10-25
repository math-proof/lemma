import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Additive.NoSmallSumDominantSet
open scoped Pointwise


/--
[NoSmallSumDominantSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/NoSmallSumDominantSet.lean)
-/
@[path]
private lemma card_add_le_card_sub_of_card_lt_six_le
-- given
  (A : Finset ℤ)
  (h_card : A.card < 6) :
-- imply
  (A + A).card ≤ (A - A).card := by
-- proof
  apply MetaMathlibExt.card_add_le_card_sub_of_card_lt_six A h_card

/--
[NoSmallSumDominantSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/NoSmallSumDominantSet.lean)
-/
@[path]
private lemma no_small_sum_dominant_le
-- given
  (A : Finset ℤ)
  (h_nonneg : ∀ x ∈ A, 0 ≤ x)
  (h_card : A.card < 6) :
-- imply
  (A + A).card ≤ (A - A).card := by
-- proof
  apply MetaMathlibExt.no_small_sum_dominant A h_nonneg h_card


-- created on 2026-10-11
