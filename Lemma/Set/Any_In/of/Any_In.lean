import sympy.sets.sets
import sympy.Basic


@[path]
private lemma limits.swap
  {A B : Set ℝ}
-- given
  (h : ∃ e ∈ A, e ∈ B) :
-- imply
  ∃ e ∈ B, e ∈ A := by
-- proof
  obtain ⟨e, hA, hB⟩ := h
  exact ⟨e, hB, hA⟩


@[path]
private lemma limits_restricted
  {S : Set ℝ}
-- given
  (h : ∃ t ∈ S, ∃ e, e ∈ S \ {t}) :
-- imply
  ∃ t ∈ S, ∃ e ∈ S \ {t}, e ∈ S \ {t} := by
-- proof
  obtain ⟨t, ht, e, he⟩ := h
  exact ⟨t, ht, e, he, he⟩


-- created on 2020-07-14
