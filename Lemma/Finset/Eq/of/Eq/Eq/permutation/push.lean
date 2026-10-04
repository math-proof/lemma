import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {p : ℕ → ℤ}
-- given
  (h₀ : (Finset.range n).image p = (Finset.range n).image (fun k : ℕ ↦ (k : ℤ)))
  (h₁ : p n = n) :
-- imply
  (Finset.range (n + 1)).image p = (Finset.range (n + 1)).image (fun k : ℕ ↦ (k : ℤ)) := by
-- proof
  rw [Finset.range_add_one, Finset.image_insert, h₀, h₁]
  simp only [Finset.image_insert]


-- created on 2020-07-08
