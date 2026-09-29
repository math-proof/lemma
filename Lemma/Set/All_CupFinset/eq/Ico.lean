import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∀ x ∈ {x : Fin n → ℕ | Finset.univ.image x = Finset.range n}, Finset.univ.image x = Finset.range n :=
-- proof
  fun _ h => h


-- created on 2026-09-27
