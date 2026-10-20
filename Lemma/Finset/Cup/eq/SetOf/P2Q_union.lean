import Mathlib.Data.Finset.Image
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ⋃ t : ℕ, {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t}
    = {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1)} := by
-- proof
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  ·
    rintro ⟨t, h, -⟩
    exact h
  ·
    intro h
    exact ⟨x (Fin.last n), h, rfl⟩


-- created on 2020-08-04
-- updated on 2026-10-17
