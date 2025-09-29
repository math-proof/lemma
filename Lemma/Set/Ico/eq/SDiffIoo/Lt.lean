import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a c : α}
-- given
  (h₀ : a < c)
  (b : α) :
-- imply
  Ico c b = Ioo a b \ Ioo a c := by
-- proof
  ext x -- Introduce arbitrary element x
  constructor -- Split into two directions
  ·
    intro h -- Forward direction: assume x ∈ Icc c b
    have hx_lt : a < x := lt_of_lt_of_le h₀ h.1
    refine ⟨⟨hx_lt, h.2⟩, ?_⟩ -- Show x ∈ Ioc a b and ¬(x ∈ Ioo a c)
    intro h' -- Assume x ∈ Ioo a c (to derive contradiction)
    exact not_le_of_gt h'.2 h.1 -- h'.2 gives x < c, but h.1 has c ≤ x
  ·
    intro h -- Backward direction: assume x ∈ Ioc a b \ Ioo a c
    have hx_ge_c : c ≤ x := by
      contrapose! h -- Contradict the assumption that x < c
      -- Now we need to show that if x < c, we reach a contradiction.
      simp_all
    exact ⟨hx_ge_c, h.1.2⟩ -- Show c ≤ x and x ≤ b


-- created on 2025-07-19
