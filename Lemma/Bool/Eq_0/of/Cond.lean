import sympy.Basic


@[main]
private lemma invert.given
  [Decidable p]
-- given
  (h : ¬p) :
-- imply
  Bool.toNat p = 0 := by
-- proof
  simp [h]


-- created on 2026-09-27
