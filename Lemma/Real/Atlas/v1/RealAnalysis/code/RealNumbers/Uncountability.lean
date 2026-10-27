import Mathlib
import Initialize.Tactic.Attr.Basic


namespace RealNumbers

/--
[Ioc_zero_one_uncountable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/Uncountability.lean)
-/
@[path]
lemma Ioc_zero_one_uncountable
-- imply
  ¬ Set.Countable (Set.Ioc (0:ℝ) 1) := by
-- proof
  rw [← Cardinal.le_aleph0_iff_set_countable, not_le]
  rwa [Cardinal.mk_Ioc_real (by norm_num : (0:ℝ) < 1)]

end RealNumbers

namespace RealNumbers

/--
[real_uncountable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/Uncountability.lean)
-/
@[path]
lemma real_uncountable
-- imply
  ¬ Set.Countable (Set.univ : Set ℝ) :=
-- proof
  Cardinal.not_countable_real

end RealNumbers


-- created on 2026-10-23
