import sympy.Basic


@[path]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : p → q) :
-- imply
  Bool.toNat p = Bool.toNat p * Bool.toNat q := by
-- proof
  by_cases hp : p
  · have hq : q := h hp
    simp [hp, hq]
  · simp [hp]


-- created on 2026-10-03
