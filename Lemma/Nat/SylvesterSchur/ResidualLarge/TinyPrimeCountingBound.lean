import Mathlib
import Initialize.Tactic.Attr.Basic
open Nat


namespace Nat.SylvesterSchur.Internal

/--
[mul_top_pow_lt_start_pow_of_two_mul_top_le_three_mul_start](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ResidualLarge/TinyPrimeCountingBound.lean)
-/
@[path]
private lemma mul_top_pow_lt_start_pow_of_two_mul_top_le_three_mul_start
  {F N k e n : ℕ} (he : e ≤ n) (hkpos : 0 < k)
  (htop : 2 * N ≤ 3 * k)
  (hconst : F * 3 ^ e < 2 ^ e * k ^ (n - e)) :
  F * N ^ e < k ^ n := by
  have htop_pow : 2 ^ e * N ^ e ≤ 3 ^ e * k ^ e := by
    simpa [Nat.mul_pow] using Nat.pow_le_pow_left htop e
  have hscaled_le : 2 ^ e * (F * N ^ e) ≤ F * (3 ^ e * k ^ e) := by
    calc
      2 ^ e * (F * N ^ e) = F * (2 ^ e * N ^ e) := by ring
      _ ≤ F * (3 ^ e * k ^ e) := Nat.mul_le_mul_left F htop_pow
  have hscaled_lt : F * (3 ^ e * k ^ e) < 2 ^ e * k ^ n := by
    calc
      F * (3 ^ e * k ^ e) = (F * 3 ^ e) * k ^ e := by ring
      _ < (2 ^ e * k ^ (n - e)) * k ^ e :=
        Nat.mul_lt_mul_of_pos_right hconst (pow_pos hkpos e)
      _ = 2 ^ e * (k ^ (n - e) * k ^ e) := by ring
      _ = 2 ^ e * k ^ ((n - e) + e) := by rw [pow_add]
      _ = 2 ^ e * k ^ n := by rw [Nat.sub_add_cancel he]
  exact Nat.lt_of_mul_lt_mul_left (hscaled_le.trans_lt hscaled_lt)

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[second_residual_tiny_primeCounting_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ResidualLarge/TinyPrimeCountingBound.lean)
-/
@[path]
lemma second_residual_tiny_primeCounting_lt_start_pow
  {n k : ℕ}
-- given
  (hn7 : 7 ≤ n)
  (hnlt38 : n < 38)
  (hk100 : 100 ≤ k) :
-- imply
  Nat.factorial n * (k + n - 1) ^ Nat.primeCounting n < k ^ n := by
-- proof
  interval_cases n
  all_goals
    apply mul_top_pow_lt_start_pow_of_two_mul_top_le_three_mul_start
    · decide
    · omega
    · omega
    · exact lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hk100 _))

end Nat.SylvesterSchur.Internal


-- created on 2026-10-23
-- updated on 2026-10-28
