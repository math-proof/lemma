import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EvenPerfectNumbers
open MetaMathlibExt


/--
[euler_characterization_of_even_perfect_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EvenPerfectNumbers.lean)
-/
@[path]
private lemma euler_characterization_of_even_perfect_numbers_eq
  {N : ℕ}
-- given
  (hN_even : Even N)
  (hN_perfect : Nat.Perfect N) :
-- imply
  ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (2 ^ p - 1) ∧
    N = 2 ^ (p - 1) * (2 ^ p - 1) := by
-- proof
  apply MetaMathlibExt.euler_characterization_of_even_perfect_numbers N hN_even hN_perfect


-- created on 2026-10-20
