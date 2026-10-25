import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.LegendreStirlingFirstKind
open MetaMathlibExt


namespace MetaMathlibExt

/--
[legendreStirlingFirst_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
lemma legendreStirlingFirst_zero
  {k : ℕ} :
-- imply
  legendreStirlingFirst 0 k = if k = 0 then 1 else 0 := by
-- proof
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_initial_row (R := ℤ) k (1 : ℤ)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[legendreStirlingFirst_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
lemma legendreStirlingFirst_succ
  {n k : ℕ} :
-- imply
  legendreStirlingFirst (n + 1) (k + 1) =
    legendreStirlingFirst n k -
    (n : ℤ) * ((n + 1 : ℕ) : ℤ) * legendreStirlingFirst n (k + 1) := by
-- proof
  simpa [legendreStirlingFirst, Nat.cast_add, Nat.cast_one] using
    jacobiStirlingFirst_recurrence (R := ℤ) n k (1 : ℤ)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[legendreStirlingFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
lemma legendreStirlingFirst_eq_zero_of_lt
  :
-- imply
  ∀ (n k : ℕ), n < k → legendreStirlingFirst n k = 0 := by
-- proof
  intro n k h
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_support (R := ℤ) n k (1 : ℤ) h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[legendreStirlingFirst_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
lemma legendreStirlingFirst_diag
  :
-- imply
  ∀ (n : ℕ), legendreStirlingFirst n n = 1 := by
-- proof
  intro n
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_diagonal (R := ℤ) n (1 : ℤ)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
