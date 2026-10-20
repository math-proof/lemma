import Mathlib
import sympy.Basic
import sympy.atlas.Order.Interval.Finset.Basic


/--
[Finset.Iio_eventually_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
private lemma Finset_Iio_eventually_nonempty_eq
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).Nonempty := by
-- proof
  apply Finset.Iio_eventually_nonempty β

/--
[Finset.Iio_eventually_card_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
private lemma Finset_Iio_eventually_card_ne_zero_eq
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).card ≠ 0 := by
-- proof
  apply Finset.Iio_eventually_card_ne_zero β

/--
[Set.Iio_eventually_ncard_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
private lemma Set_Iio_eventually_ncard_ne_zero_eq
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Set.Iio n).ncard ≠ 0 := by
-- proof
  apply Set.Iio_eventually_ncard_ne_zero β


-- created on 2026-10-20
