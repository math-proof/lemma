import sympy.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  (decide p).toNat = Bool.toNat p := by
-- proof
  simp


-- created on 2025-10-01
