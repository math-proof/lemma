import sympy.core.mul
import sympy.Basic


@[path]
private lemma main
-- given
  (s s' : List ℕ)
  (h : s.length = s'.length) :
-- imply
  s.zipWith Nat.lcm s' = s'.zipWith Nat.lcm s := by
-- proof
  induction s generalizing s' with
  | nil =>
    cases s'
    ·
      rfl
    ·
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      simp [List.zipWith, Nat.lcm_comm]
      exact ih s' (Nat.succ_injective h)


-- created on 2026-10-07
