import sympy.sets.sets
import sympy.Basic


@[main]
private lemma index
  {n : ℕ}
  {x : ℕ → ℤ}
  {j : ℤ}
-- given
  (h : (Finset.range n).biUnion (fun k => {x k}) = Finset.Ico 0 (n : ℤ))
  (hj : j ∈ Finset.Ico 0 (n : ℤ)) :
-- imply
  (∑ k ∈ Finset.range n, (if x k = j then 1 else 0) * k) ∈ Finset.range n ∧ x (∑ k ∈ Finset.range n, (if x k = j then 1 else 0) * k) = j := by
-- proof
  rw [Finset.biUnion_singleton] at h
  have hinj : Set.InjOn x (Finset.range n) := Finset.card_image_iff.mp (by rw [h]; simp)
  obtain ⟨k0, hk0, hxk⟩ : ∃ k0 ∈ Finset.range n, x k0 = j := by
    rw [← h] at hj
    simpa using hj
  have hs : ∑ k ∈ Finset.range n, (if x k = j then 1 else 0) * k = k0 := by
    rw [Finset.sum_eq_single k0]
    · simp [hxk]
    · intro b hb hne
      rw [if_neg (fun e => hne (hinj hb hk0 (e.trans hxk.symm)))]
      simp
    · intro h'
      exact absurd hk0 h'
  rw [hs]
  exact ⟨hk0, hxk⟩


-- created on 2026-09-27
