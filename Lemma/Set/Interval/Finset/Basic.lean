import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Finset.Iio_eventually_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
lemma Finset.Iio_eventually_nonempty
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).Nonempty :=
-- proof
  let ⟨b, hb⟩ := exists_ne (⊥ : β)
  ⟨b, fun n hn => by simp [ne_bot_of_le_ne_bot hb hn]⟩

/--
[Finset.Iio_eventually_card_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
lemma Finset.Iio_eventually_card_ne_zero
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Finset.Iio n).card ≠ 0 :=
-- proof
  let ⟨b, hb⟩ := Iio_eventually_nonempty β
  ⟨b, fun n hn => by simp [nonempty_iff_ne_empty.1 <| hb n hn]⟩

/--
[Set.Iio_eventually_ncard_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/Interval/Finset/Basic.lean)
-/
@[path]
lemma Set.Iio_eventually_ncard_ne_zero
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  ∃ (b : β), ∀ n ≥ b, (Set.Iio n).ncard ≠ 0 :=
-- proof
  let ⟨b, hb⟩ := Finset.Iio_eventually_card_ne_zero β
  ⟨b, fun n hn => by rw [← Finset.coe_Iio, Set.ncard_coe_finset]; exact hb n hn⟩


-- created on 2026-10-20
-- updated on 2026-10-26
