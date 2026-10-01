import sympy.tensor.index_of
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i j : ℕ}
  {x : ℕ → ℤ}
-- given
  (h : (Finset.range n).image x = Finset.Ico 0 (n : ℤ))
  (hi : i < n)
  (hj : j < n) :
-- imply
  (if IndexOf.index (i : ℤ) x n = IndexOf.index (j : ℤ) x n then (1 : ℤ) else 0) = if i = j then 1 else 0 := by
-- proof
  have ex : ∀ t : ℕ, t < n → ∃ k < n, x k = (t : ℤ) := by
    intro t ht
    have hm : (t : ℤ) ∈ (Finset.range n).image x := by
      rw [h, Finset.mem_Ico]
      exact ⟨by omega, by omega⟩
    obtain ⟨k, hk, e⟩ := Finset.mem_image.mp hm
    exact ⟨k, Finset.mem_range.mp hk, e⟩
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij, if_neg]
    intro e
    apply hij
    have := congrArg x e
    rw [IndexOf.get_index (ex i hi), IndexOf.get_index (ex j hj)] at this
    exact_mod_cast this


-- created on 2020-10-27
