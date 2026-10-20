import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (σ : Equiv.Perm (Fin n)) :
-- imply
  Finset.image (σ : Fin n → Fin n) Finset.univ = Finset.univ := by
-- proof
  simp


-- created on 2020-11-04
-- updated on 2026-10-17
