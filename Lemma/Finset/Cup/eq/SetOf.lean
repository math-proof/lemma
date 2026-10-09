import sympy.sets.sets
import sympy.Basic


@[path]
private lemma P2Q_union
  {n : ℕ} :
-- imply
  ⋃ t : ℕ, {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t} = {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1)} := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, h, -⟩
    exact h
  · intro h
    exact ⟨_, h, rfl⟩


-- created on 2026-09-27
