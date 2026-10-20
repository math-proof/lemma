import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.SumTwoCoprimeSquares
open MetaMathlibExt.SumTwoCoprimeSquares


/--
[sum_two_coprime_squares_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/SumTwoCoprimeSquares.lean)
-/
@[path]
private lemma sum_two_coprime_squares_characterization_eq
  {d : ℕ}
-- given
  (hd : 2 < d) :
-- imply
  ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a ^ 2 + b ^ 2 = d) ↔
    ∃ q : ℕ, (∀ p ∈ q.primeFactors, p % 4 = 1) ∧ (d = q ∨ d = 2 * q)) := by
-- proof
  apply MetaMathlibExt.SumTwoCoprimeSquares.sum_two_coprime_squares_characterization d hd


-- created on 2026-10-20
