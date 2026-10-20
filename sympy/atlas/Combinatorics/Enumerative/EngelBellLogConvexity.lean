/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EngelBellLogConvexity.lean -/

import Mathlib.Combinatorics.Enumerative.Bell
import sympy.atlas.Combinatorics.Enumerative.BellTuranIdentity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace MetaMathlibExt

/-- Engel's log-convexity inequality for Bell numbers, Eq. (E2).

Horst Alzer, "On Engel's Inequality for Bell Numbers,"
Journal of Integer Sequences 22 (2019).
Source: <https://cs.uwaterloo.ca/journals/JIS/VOL22/Alzer/alzer6.tex>,
lines 79--104, where `B_n` is defined as the Bell number and Eq. (E2) states
`B_n^2 ≤ B_{n-1} B_{n+1}` for every integer `n ≥ 1`.
Source file SHA-256:
`03a0712f6a473227541845886072d039e644d950ee6f591a456b1cffcd1b9f46`.
The source attributes this inequality to K. Engel, "On the average rank of an
element in a filter of the partition lattice," J. Combin. Theory Ser. A 65
(1994), 67--78.

Stable concept id: `jis_grounded_0ea6ed8edd46a1ad43f4d963`.

Scope: this is the complete selected non-strict theorem as stated in Eq. (E2);
it is not Alzer's later strict refinement nor the series identity.

Proves `Wanted` entry `engel_bell_log_convexity`.
-/
theorem engel_bell_log_convexity (n : ℕ) (hn : 1 ≤ n) :
    (Nat.bell n) ^ 2 ≤ Nat.bell (n - 1) * Nat.bell (n + 1) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    norm_num [Nat.bell_zero, Nat.bell_one, Nat.bell_two]
  · have h : (Nat.bell n : ℝ) ^ 2 ≤ (Nat.bell (n - 1) : ℝ) * (Nat.bell (n + 1) : ℝ) := by
      rw [← sub_nonneg, bell_turan_identity n h2]
      exact mul_nonneg (by positivity)
        (tsum_nonneg fun k => Finset.sum_nonneg fun j _ => by positivity)
    exact_mod_cast h

end MetaMathlibExt
