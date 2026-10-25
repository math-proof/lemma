/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
/-!
# Narayana numbers.
-/


namespace MetaMathlibExt

/-- Narayana number `N(n, k)` for positive `n` and `k` (concept
`jis_sem_6a8b07ab7f79ed673976aec8`; source statements
`jis_5e63e8dec0bd7e8127ff4261` and `jis_6939ec31631161285ec502bd`). -/
def narayana (n k : {n : ℕ // 0 < n}) : ℕ :=
  (Nat.choose n.val k.val * Nat.choose n.val (k.val - 1)) / n.val

end MetaMathlibExt
