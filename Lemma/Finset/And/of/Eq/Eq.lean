import sympy.sets.sets
import sympy.Basic


@[path]
private lemma index_general
  {n j : ℕ}
  {x a : ℕ → ℤ}
-- given
  (h₀ : ((Finset.range n).biUnion fun k => {a k}).card = n)
  (h₁ : (Finset.range n).biUnion (fun k => {x k}) = (Finset.range n).biUnion (fun k => {a k}))
  (hj : j ∈ Finset.range n) :
-- imply
  (∑ k ∈ Finset.range n, (if x k = a j then 1 else 0) * k) ∈ Finset.range n ∧ x (∑ k ∈ Finset.range n, (if x k = a j then 1 else 0) * k) = a j := by
-- proof
  simp only [Finset.biUnion_singleton] at h₀ h₁
  have hinj : Set.InjOn x (Finset.range n) := Finset.card_image_iff.mp (by rw [h₁, h₀]; simp)
  obtain ⟨k0, hk0, hxk⟩ : ∃ k0 ∈ Finset.range n, x k0 = a j := by
    have : a j ∈ (Finset.range n).image x := by rw [h₁]; exact Finset.mem_image_of_mem a hj
    simpa using this
  have hs : ∑ k ∈ Finset.range n, (if x k = a j then 1 else 0) * k = k0 := by
    rw [Finset.sum_eq_single k0]
    · simp [hxk]
    · intro b hb hne
      rw [if_neg (fun e => hne (hinj hb hk0 (e.trans hxk.symm)))]
      simp
    · intro h'
      exact absurd hk0 h'
  rw [hs]
  exact ⟨hk0, hxk⟩


-- created on 2020-07-22
