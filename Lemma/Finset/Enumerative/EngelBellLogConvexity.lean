import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.BellTuranIdentity
import Lemma.Finset.Enumerative.BellTuranIdentity


namespace MetaMathlibExt

/--
[engel_bell_log_convexity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EngelBellLogConvexity.lean)
-/
@[path]
lemma engel_bell_log_convexity
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (Nat.bell n) ^ 2 ≤ Nat.bell (n - 1) * Nat.bell (n + 1) := by
-- proof
  obtain h1 | h2 := Nat.lt_or_ge n 2
  · obtain rfl : n = 1 := by omega
    norm_num [Nat.bell_zero, Nat.bell_one, Nat.bell_two]
  · have h : (Nat.bell n : ℝ) ^ 2 ≤ (Nat.bell (n - 1) : ℝ) * (Nat.bell (n + 1) : ℝ) := by
    rw [← sub_nonneg, bell_turan_identity n h2]
    exact mul_nonneg (by positivity)
      (tsum_nonneg fun k => Finset.sum_nonneg fun j _ => by positivity)
    exact_mod_cast h

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
