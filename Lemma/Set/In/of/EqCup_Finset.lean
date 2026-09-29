import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ}
  {x : ℕ → ℤ}
  {s : Finset ℤ}
-- given
  (h₀ : (Finset.range n).biUnion (fun k => {x k}) = s)
  (h₁ : i < n) :
-- imply
  x i ∈ s := by
-- proof
  rw [← h₀]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr h₁, Finset.mem_singleton_self _⟩


-- created on 2026-09-27
