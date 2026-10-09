import sympy.Basic


@[path]
private lemma main
  [Decidable p]
-- given
  (h : Bool.toNat p > 0) :
-- imply
  p := by
-- proof
  by_contra hp
  simp [hp] at h


-- created on 2023-11-05
