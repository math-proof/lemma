import sympy.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = if p then
    1
  else
    0 := by
-- proof
  unfold Bool.toNat
  simp


-- created on 2025-04-05
