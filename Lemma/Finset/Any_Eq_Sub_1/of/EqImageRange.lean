import Lemma.Set.In_Range.of.Lt
open Set


@[main]
private lemma main
  [NeZero (n : ℕ)]
  {p : ℕ → ℕ}
-- given
  (h : (Finset.range n).image p = Finset.range n) :
-- imply
  ∃ i ∈ Finset.range n, p i = n - 1 := by
-- proof
  have hmem : n - 1 ∈ (Finset.range n).image p := by
    rw [h]
    exact In_Range.of.Lt (Nat.sub_one_lt (NeZero.ne n))
  simpa [Finset.mem_image] using hmem


-- created on 2020-08-31
-- updated on 2026-09-09
