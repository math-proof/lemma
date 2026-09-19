import sympy.Basic


@[main]
private lemma main
  {s : Finset ℕ}
  {f : ℕ → ℤ}
-- given
  (h : ∀ i ∈ s, 0 ≤ f i) :
-- imply
  (∑ i ∈ s, f i).toNat = ∑ i ∈ s, (f i).toNat := by
-- proof
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (Finset.sum_nonneg h), Nat.cast_sum]
  exact Finset.sum_congr rfl fun i hi => (Int.toNat_of_nonneg (h i hi)).symm


-- created on 2026-09-18
