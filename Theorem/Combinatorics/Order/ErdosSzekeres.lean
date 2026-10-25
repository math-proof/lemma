/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-!
# Erdős–Szekeres monotone subsequence theorem

Every injective real sequence of length `(r - 1) * (s - 1) + 1` contains an
increasing subsequence of length `r` or a decreasing subsequence of length `s`.

Source: P. Erdős and G. Szekeres, “A combinatorial problem in geometry,”
_Compositio Mathematica_ 2 (1935), 463–470; the two-parameter
monotone-subsequence bound is proved on p. 468.
NUMDAM record: https://www.numdam.org/item/CM_1935__2__463_0/.
-/

/-- `k - 1 < k` for positive `k`. -/
theorem sub_one_lt_of_pos {k : ℕ} (hk : 0 < k) : k - 1 < k := by omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres
