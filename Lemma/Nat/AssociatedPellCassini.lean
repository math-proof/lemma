import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.AssociatedPellCassini
open MetaMathlibExt


/--
[associated_pell_cassini_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AssociatedPellCassini.lean)
-/
@[path]
private lemma associated_pell_cassini_identity_eq
  {Q : ℕ → ℤ}
  {k : ℕ}
-- given
  (hQ_zero : Q 0 = 1)
  (hQ_one : Q 1 = 1)
  (hQ_rec : ∀ n : ℕ, Q (n + 2) = 2 * Q (n + 1) + Q n)
  (hk : 1 ≤ k) :
-- imply
  Q (k - 1) * Q (k + 1) =
      Q k ^ 2 + 2 * (-1 : ℤ) ^ (k - 1) := by
-- proof
  apply MetaMathlibExt.associated_pell_cassini_identity Q hQ_zero hQ_one hQ_rec k hk


-- created on 2026-10-20
