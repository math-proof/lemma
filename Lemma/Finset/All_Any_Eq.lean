import sympy.sets.sets
import sympy.Basic


@[main]
private lemma permutation
  {n : ℕ}
  {a : Fin (n + 1) → ℤ} :
-- imply
  ∀ p ∈ {p : Fin (n + 1) → ℤ | Finset.univ.image p = Finset.univ.image a}, ∃ i, p i = a (Fin.last n) := by
-- proof
  intro p hp
  have hm : a (Fin.last n) ∈ Finset.univ.image p := by
    rw [hp]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simpa using hm


-- created on 2026-09-27
