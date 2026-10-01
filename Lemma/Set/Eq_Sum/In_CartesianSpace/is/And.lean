import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {t : Fin n → ℤ}
  {m k : ℤ}
-- given
  (h : k ≥ 0) :
-- imply
  (∑ i, t i = m - k ∧ t ∈ Set.univ.pi fun _ => Set.Ico 0 (m + 1)) ↔
    (∑ i, t i = m - k ∧ t ∈ Set.univ.pi fun _ => Set.Ico 0 (m - k + 1)) := by
-- proof
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨hs, fun i _ => ⟨(ht i (Set.mem_univ i)).1, ?_⟩⟩
    have := Finset.single_le_sum (fun j _ => (ht j (Set.mem_univ j)).1) (Finset.mem_univ i)
    linarith
  · rintro ⟨hs, ht⟩
    exact ⟨hs, fun i _ => ⟨(ht i (Set.mem_univ i)).1, by linarith [(ht i (Set.mem_univ i)).2]⟩⟩


-- created on 2026-09-27
