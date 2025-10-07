import sympy.Basic


@[main]
private lemma main
  [Decidable p]
-- given
  (h : p) :
-- imply
  Bool.toNat (¬p) = 0 := by
-- proof
  simp [h]


-- created on 2025-04-27
