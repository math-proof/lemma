import sympy.sets.sets
import sympy.Basic


@[main]
private lemma index
  {n : ℕ}
  {x : ℕ → ℤ}
  {j : ℤ}
-- given
  (h₀ : (Finset.range n).biUnion (fun k => {x k}) = Finset.Ico 0 (n : ℤ))
  (h₁ : j ∈ Finset.Ico 0 (n : ℤ)) :
-- imply
  ∃ k ∈ Finset.range n, x k = j := by
-- proof
  rw [Finset.biUnion_singleton] at h₀
  have hm : j ∈ (Finset.range n).image x := h₀ ▸ h₁
  simpa using hm


@[main]
private lemma index_general
  {n : ℕ}
  {x : ℕ → ℤ}
  {j : ℤ}
-- given
  (h₀ : (Finset.range n).biUnion (fun k => {x k}) = Finset.Ico 0 (n : ℤ))
  (h₁ : j ∈ Finset.Ico 0 (n : ℤ)) :
-- imply
  ∃ k ∈ Finset.range n, x k = j := by
-- proof
  rw [Finset.biUnion_singleton] at h₀
  have hm : j ∈ (Finset.range n).image x := h₀ ▸ h₁
  simpa using hm


-- created on 2020-10-23
