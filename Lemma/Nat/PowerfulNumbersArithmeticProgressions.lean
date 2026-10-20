import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PowerfulNumbersArithmeticProgressions
open MetaMathlibExt


/--
[arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerfulNumbersArithmeticProgressions.lean)
-/
@[path]
private lemma arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general_eq
  {k : ℕ} :
-- imply
  ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
    ∀ i : ℕ, i < k → Nat.IsKFull 2 (a + i * d) := by
-- proof
  apply MetaMathlibExt.arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general k

/--
[arbitrarily_long_arithmetic_progressions_of_powerful_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerfulNumbersArithmeticProgressions.lean)
-/
@[path]
private lemma arbitrarily_long_arithmetic_progressions_of_powerful_numbers_eq
  {k : ℕ}
-- given
  (hk : 3 ≤ k) :
-- imply
  ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
    ∀ i : ℕ, i < k →
    ∀ p : ℕ, p.Prime → p ∣ a + i * d → p ^ 2 ∣ a + i * d := by
-- proof
  apply MetaMathlibExt.arbitrarily_long_arithmetic_progressions_of_powerful_numbers k hk


-- created on 2026-10-20
