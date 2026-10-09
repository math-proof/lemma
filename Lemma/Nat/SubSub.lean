import sympy.Basic


@[path]
private lemma Comm
  {a b c : ℕ} :
-- imply
  a - b - c = a - c - b := by
-- proof
  simp [Nat.sub_sub, add_comm]


-- created on 2025-10-12
