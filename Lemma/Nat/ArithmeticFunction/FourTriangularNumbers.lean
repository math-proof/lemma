import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.FourTriangularNumbers
open MetaMathlibExt


/--
[four_triangular_numbers_eq_divisor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/FourTriangularNumbers.lean)
-/
@[path]
private lemma four_triangular_numbers_eq_divisor_sum_eq
  {j : ℕ} :
-- imply
  Fintype.card { t : Fin 4 → Fin (j + 1) //
    (∑ i, ((t i).val * ((t i).val + 1) / 2)) = j } =
    ∑ d ∈ Nat.divisors (2 * j + 1), d := by
-- proof
  apply MetaMathlibExt.four_triangular_numbers_eq_divisor_sum j


-- created on 2026-10-20
