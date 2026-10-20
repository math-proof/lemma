import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GeneralizedPellNumbers
open MetaMathlibExt


/--
[generalized_pell_eq_two_colored_compositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedPellNumbers.lean)
-/
@[path]
private lemma generalized_pell_eq_two_colored_compositions_eq
  {k n : ℕ}
  {P : ℤ → ℕ}
-- given
  (hk : 2 ≤ k)
  (hn : 1 ≤ n)
  (hPzero : ∀ m : ℤ, 2 - (k : ℤ) ≤ m → m ≤ 0 → P m = 0)
  (hPone : P 1 = 1)
  (hPrec : ∀ m : ℤ, 2 ≤ m → P m = 2 * P (m - 1) + ∑ i : Fin (k - 1), P (m - (((i : ℕ) : ℤ) + 2))) :
-- imply
  Set.ncard {
    c : Σ ℓ : Fin (n + 1), Fin ℓ → Fin (k + 1) |
    ∑ j : Fin c.1, (if (c.2 j).val ≤ 1 then 1 else (c.2 j).val) = n
    } = P ((n + 1 : ℕ) : ℤ) := by
-- proof
  apply MetaMathlibExt.generalized_pell_eq_two_colored_compositions k n hk hn P hPzero hPone hPrec


-- created on 2026-10-20
