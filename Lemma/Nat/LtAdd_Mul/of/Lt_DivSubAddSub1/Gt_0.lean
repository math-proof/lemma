import sympy.concrete.expr_with_limits
import sympy.Basic


@[main]
private lemma main
  {Z b d m : ℕ}
-- given
  (hd : 0 < d)
  (hm : m < (Z - b + d - 1) / d) :
-- imply
  b + m * d < Z := by
-- proof
  have h1 : (m + 1) * d ≤ Z - b + d - 1 := (Nat.le_div_iff_mul_le hd).mp hm
  rw [Nat.add_mul, one_mul] at h1
  omega


-- created on 2026-10-07
