import Lemma.Set.Any.Eq.of.Eq_Card
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {S : Finset (Fin k → ℤ)}
-- given
  (h : S.card = n) :
-- imply
  ∃ x : ℕ → Fin k → ℤ, S = (Finset.range n).image x ∧ S.card = n := by
-- proof
  obtain ⟨x, _, hx⟩ := Set.Any.Eq.of.Eq_Card h
  exact ⟨x, hx, h⟩


-- created on 2021-02-02
