import sympy.Basic


@[main]
private lemma main
-- given
  (h : p → q) :
-- imply
  p ↔ p ∧ q := by
-- proof
  -- Split the equivalence into two implications
  constructor
  ·
    -- Prove p → p ∧ q
    intro hp
    -- Use the given implication h to derive q from p
    exact ⟨hp, h hp⟩
  ·
    -- Prove p ∧ q → p
    intro hpq
    -- Extract p from the conjunction p ∧ q
    exact hpq.1


-- created on 2025-04-17
