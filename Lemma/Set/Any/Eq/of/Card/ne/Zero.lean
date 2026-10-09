import Lemma.Set.Any.Eq.of.Eq_Card
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {k : ℕ}
  {S : Finset (Fin k → ℤ)}
-- given
  (_h : S.card ≠ 0) :
-- imply
  ∃ x : ℕ → Fin k → ℤ, S = (Finset.range S.card).image x := by
-- proof
  obtain ⟨x, _, hx⟩ := Set.Any.Eq.of.Eq_Card rfl
  exact ⟨x, hx⟩


-- created on 2021-02-03
