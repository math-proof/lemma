import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TriangularStripTilings
open MetaMathlibExt


/--
[quarter_period_factorizations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TriangularStripTilings.lean)
-/
@[path]
private lemma quarter_period_factorizations_eq
  {Q : ℕ → ℕ}
  {m : ℕ}
-- given
  (hQ0 : Q 0 = 1)
  (hQ1 : Q 1 = 1)
  (hQ2 : Q 2 = 4)
  (hQrec : ∀ n : ℕ, 3 ≤ n → Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3))
  (hm : 1 ≤ m) :
-- imply
  Q (4 * m) =
    (2 * Q (2 * m - 1) + 1) * (2 * Q (2 * m) - 1) ∧
    Q (4 * m + 1) = (2 * Q (2 * m) - 1) ^ 2 ∧
    Q (4 * m + 2) =
    2 * (Q (2 * m - 1) + Q (2 * m)) *
    (Q (2 * m) + Q (2 * m + 1)) ∧
    Q (4 * m + 3) =
    2 * (Q (2 * m) + Q (2 * m + 1)) ^ 2 := by
-- proof
  apply MetaMathlibExt.quarter_period_factorizations Q hQ0 hQ1 hQ2 hQrec m hm


-- created on 2026-10-20
