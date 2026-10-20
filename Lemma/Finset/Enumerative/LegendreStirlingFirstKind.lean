import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LegendreStirlingFirstKind
open MetaMathlibExt


/--
[legendreStirlingFirst_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_zero_eq
  {k : ℕ} :
-- imply
  legendreStirlingFirst 0 k = if k = 0 then 1 else 0 := by
-- proof
  apply MetaMathlibExt.legendreStirlingFirst_zero k

/--
[legendreStirlingFirst_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_succ_eq
  {n k : ℕ} :
-- imply
  legendreStirlingFirst (n + 1) (k + 1) =
    legendreStirlingFirst n k -
    (n : ℤ) * ((n + 1 : ℕ) : ℤ) * legendreStirlingFirst n (k + 1) := by
-- proof
  apply MetaMathlibExt.legendreStirlingFirst_succ n k

/--
[legendreStirlingFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_eq_zero_of_lt_eq
  :
-- imply
  ∀ (n k : ℕ), n < k → legendreStirlingFirst n k = 0 := by
-- proof
  apply MetaMathlibExt.legendreStirlingFirst_eq_zero_of_lt

/--
[legendreStirlingFirst_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_diag_eq
  :
-- imply
  ∀ (n : ℕ), legendreStirlingFirst n n = 1 := by
-- proof
  apply MetaMathlibExt.legendreStirlingFirst_diag


-- created on 2026-10-20
