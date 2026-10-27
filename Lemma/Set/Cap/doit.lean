import Mathlib.Data.Int.Interval
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddCommMonoid α]
  {a : ℤ}
  {n : ℕ}
  {f : ℤ → α} :
-- imply
  ∑ i ∈ Finset.Ico a (a + n), f i = ∑ t ∈ Finset.range n, f (a + t) := by
-- proof
  rw [Int.Ico_eq_finset_map, add_sub_cancel_left, Int.toNat_natCast]
  simp [Finset.sum_map, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]


-- created on 2026-10-11
-- updated on 2026-10-26
