import sympy.core.mul
import sympy.Basic


@[path]
private lemma main
-- given
  (k : ℕ) :
-- imply
  (List.replicate k (1 : ℕ)).zipWith Nat.lcm (List.replicate k 1) =
      List.replicate k 1 := by
-- proof
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    simp [List.replicate_succ, Nat.lcm_self]


-- created on 2026-10-07
