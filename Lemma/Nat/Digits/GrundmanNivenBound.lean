import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.GrundmanNivenBound
open MathlibExt.NumberTheory.Digits.GrundmanNivenBoundWanted


/--
[grundman_consecutive_niven_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/GrundmanNivenBound.lean)
-/
@[path]
private lemma grundman_consecutive_niven_bound_eq
  {b a : ℕ}
-- given
  (hb : 2 ≤ b)
  (ha : 0 < a) :
-- imply
  ∃ i : ℕ, i ≤ 2 * b ∧
    ¬ ((Nat.digits b (a + i)).sum ∣ a + i) := by
-- proof
  apply MathlibExt.NumberTheory.Digits.GrundmanNivenBoundWanted.grundman_consecutive_niven_bound b a hb ha


-- created on 2026-10-20
