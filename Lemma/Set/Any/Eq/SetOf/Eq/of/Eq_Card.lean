import Lemma.Set.Any.Eq.of.Eq_Card
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n k : ℕ}
  {S : Finset (Fin k → ℤ)}
-- given
  (h : S.card = n) :
-- imply
  ∃ x : ℕ → Fin k → ℤ,
    ((Finset.range n).image x).card = n ∧ S = (Finset.range n).image x := by
-- proof
  obtain ⟨x, hdistinct, hx⟩ := Set.Any.Eq.of.Eq_Card h
  have hinj : Set.InjOn x (Finset.range n : Set ℕ) := by
    intro i hi j hj he
    have hii : i < n := Finset.mem_range.mp hi
    have hjj : j < n := Finset.mem_range.mp hj
    by_cases hlt : i < j
    · exact False.elim ((hdistinct j hjj i (by omega)) he.symm)
    · by_cases hlt' : j < i
      · exact False.elim ((hdistinct i hii j (by omega)) he)
      · omega
  have hc : ((Finset.range n).image x).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  exact ⟨x, hc, hx⟩


-- created on 2021-02-02
-- updated on 2023-11-11
