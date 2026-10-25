/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SteuerwaldThreePerfect.lean -/

/-
# Tests for Pillai equations and Steuerwald's theorem
-/

import Lemma.Nat.SteuerwaldThreePerfect


example :
    (∀ a b : ℕ, (2 : ℤ) ^ a - 3 ^ b = -1 ↔
        (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2)) ∧
      (∀ a b c : ℕ, (2 : ℤ) ^ a - 3 ^ b = 2 ^ c - 1 ↔
        (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 4 ∧ b = 2 ∧ c = 3) ∨
        (b = 0 ∧ c = a)) :=
  MetaMathlibExt.pillai_equations_two_pow_three_pow

