import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {x : ℕ → ℂ}
-- given
  (h : k ∈ Finset.Ico 2 (n + 1)) :
-- imply
  ∑ t ∈ Finset.powersetCard k (Finset.range (n + 1)), ∏ i ∈ t, x i = x n * ∑ t ∈ Finset.powersetCard (k - 1) (Finset.range n), ∏ i ∈ t, x i + ∑ t ∈ Finset.powersetCard k (Finset.range n), ∏ i ∈ t, x i := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by simp only [Finset.mem_Ico] at h; omega⟩
  have hn : ∀ t ∈ Finset.powersetCard m (Finset.range n), n ∉ t := fun t ht hm =>
    Finset.notMem_range_self ((Finset.mem_powersetCard.mp ht).1 hm)
  rw [Finset.range_add_one, Finset.powersetCard_succ_insert Finset.notMem_range_self, Finset.sum_union, Finset.sum_image]
  ·
    rw [Nat.add_sub_cancel, add_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.prod_insert (hn t ht)]
  ·
    intro s hs t ht e
    rw [← Finset.erase_insert (hn s hs), ← Finset.erase_insert (hn t ht)]
    exact congrArg (fun u => Finset.erase u n) e
  ·
    rw [Finset.disjoint_left]
    intro t h1 h2
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp h2
    exact Finset.notMem_range_self ((Finset.mem_powersetCard.mp h1).1 (Finset.mem_insert_self n s))


-- created on 2026-10-08
