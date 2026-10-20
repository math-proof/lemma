import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d < 0) :
-- imply
  n % d ∈ Finset.Ico 0 (-d) := by
-- proof
  rw [Finset.mem_Ico]
  refine ⟨Int.emod_nonneg n h₀.ne, ?_⟩
  simpa [abs_of_neg h₀] using Int.emod_lt_abs n h₀.ne


-- created on 2021-04-22
-- updated on 2026-10-17
