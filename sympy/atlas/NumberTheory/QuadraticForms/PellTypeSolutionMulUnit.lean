/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/PellTypeSolutionMulUnit.lean -/

import Mathlib.Tactic.LinearCombination

namespace MetaMathlibExt

/-! # Composing a Pell-type solution with a norm-one unit
-/

/--
Multiplying a solution `(T, U)` of `a * T ^ 2 - b * U ^ 2 = c` by a unit
`(x, y)` of `x ^ 2 - a * b * y ^ 2 = 1` yields the solution
`(T * x + b * U * y, a * T * y + U * x)`.

Source: E. L. Roettger and H. C. Williams, "Some Remarks Concerning the
Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025),
Article 25.2.5, Theorem (label PellTheorem, an observation of Euler),
equation (label DioEq), lines 605–614,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex>

The source iterates this step under the assumption that `ab > 1` is not a
square to obtain infinitely many solutions. That infinitude claim needs further
nondegeneracy hypotheses (for `T = U = c = 0` every iterate is `(0, 0)`) and is
not formalized here; the single-step identity is pure algebra
(multiplicativity of the norm form) needing no hypotheses beyond the two
equations.
Proves `Wanted` entry `pellType_solution_mul_unit`.
-/
theorem pellType_solution_mul_unit
    (a b c T U x y : ℤ)
    (hsol : a * T ^ 2 - b * U ^ 2 = c)
    (hunit : x ^ 2 - a * b * y ^ 2 = 1) :
    a * (T * x + b * U * y) ^ 2 - b * (a * T * y + U * x) ^ 2 = c := by
  linear_combination (x ^ 2 - a * b * y ^ 2) * hsol + c * hunit

end MetaMathlibExt
