import sympy.Basic


@[path]
private lemma invert
  [Decidable p]
-- given
  (h : Bool.toNat p = 0) :
-- imply
  ¬p := by
-- proof
  intro hp
  simp [hp] at h


-- created on 2023-11-05
