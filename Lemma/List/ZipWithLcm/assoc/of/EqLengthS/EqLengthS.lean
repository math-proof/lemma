import sympy.core.mul
import sympy.Basic


@[main]
private lemma main
-- given
  (s s' s'' : List ℕ)
  (h₁ : s.length = s'.length)
  (h₂ : s'.length = s''.length) :
-- imply
  (s.zipWith Nat.lcm s').zipWith Nat.lcm s'' =
      s.zipWith Nat.lcm (s'.zipWith Nat.lcm s'') := by
-- proof
  induction s generalizing s' s'' with
  | nil =>
    cases s'
    ·
      cases s''
      ·
        rfl
      ·
        cases h₂
    ·
      cases h₁
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h₁
    | cons n' s' =>
      cases s'' with
      | nil =>
        cases h₂
      | cons n'' s'' =>
        simp [List.zipWith, Nat.lcm_assoc]
        exact ih s' s'' (Nat.succ_injective h₁) (Nat.succ_injective h₂)


-- created on 2026-10-07
