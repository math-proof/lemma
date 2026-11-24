import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Decidable p] [Decidable q] :
-- imply
  (decide p).toNat + (decide q).toNat = (decide (p ∨ q)).toNat + (decide (p ∧ q)).toNat := by
-- proof
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]


-- created on 2018-08-03
-- updated on 2026-11-24
