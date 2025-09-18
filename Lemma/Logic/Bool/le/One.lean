import Lemma.Basic


@[main]
private lemma main
  [Decidable p]:
-- imply
  Bool.toNat p ≤ 1 := by
-- proof
  by_cases h : p <;>
    simp [h]


-- created on 2025-07-20
