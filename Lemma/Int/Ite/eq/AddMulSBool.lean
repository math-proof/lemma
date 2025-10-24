import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Ring α]
-- given
  (a b : α) :
-- imply
  (if p then
    a
  else
    b) = Bool.toNat p * a + (Bool.toNat ¬p) * b := by
-- proof
  split_ifs <;>
  ·
    simp_all


-- created on 2025-07-20
