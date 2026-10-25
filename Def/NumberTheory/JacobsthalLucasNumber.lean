/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/JacobsthalLucasNumber.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Jacobsthal–Lucas numbers

This module defines the standard Jacobsthal–Lucas sequence, OEIS A014551.

Sources:

* Kenan Kaygisiz and Adem Şahin, *Generalized Bivariate Lucas p-Polynomials and Hessenberg
  Matrices*, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Kaygisiz/kaygisiz3.tex>.
* Yash Puri and Thomas Ward, *Arithmetic and Growth of Periodic Orbits*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

JIS concept: `jis_sem_bbf5bfb8ea55b99401341187`.
-/


namespace MetaMathlibExt

/-- The Jacobsthal–Lucas numbers `2, 1, 5, 7, 17, …` (OEIS A014551), satisfying
`j_(n+2) = j_(n+1) + 2 * j_n`. -/
def jacobsthalLucasNumber : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => jacobsthalLucasNumber (n + 1) + 2 * jacobsthalLucasNumber n

end MetaMathlibExt
