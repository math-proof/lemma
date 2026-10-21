import Mathlib
import sympy.Basic


/--
[roth_succ_le_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  n + 1 ≤ 2 ^ n := by
-- proof
  induction n with
  | zero => omega
  | succ n ih =>
    if hn0 : n = 0 then
      subst n
      norm_num
    else
      calc
        _ ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih (Nat.pos_of_ne_zero hn0))
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          ring


-- created on 2026-10-21
