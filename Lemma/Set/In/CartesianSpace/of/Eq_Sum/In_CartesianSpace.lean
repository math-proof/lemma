import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {t : Fin n → ℝ}
  {m : ℝ}
-- given
  (h₀ : ∑ i, t i = m)
  (h₁ : t ∈ Set.univ.pi fun _ => Set.Ici 0) :
-- imply
  t ∈ Set.univ.pi fun _ => Set.Icc 0 m := by
-- proof
  intro i _
  refine ⟨h₁ i (Set.mem_univ i), ?_⟩
  rw [← h₀]
  exact Finset.single_le_sum (fun j _ => (h₁ j (Set.mem_univ j) : (0 : ℝ) ≤ t j)) (Finset.mem_univ i)


-- created on 2026-09-27
