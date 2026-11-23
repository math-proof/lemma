import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℕ}
-- given
  (h_ge : a ≥ b)
  (h_eq : a - b = 0) :
-- imply
  a = b := by
-- proof
  apply le_antisymm (Nat.le_of_sub_eq_zero h_eq) h_ge


-- created on 2025-04-11
-- updated on 2026-11-23
