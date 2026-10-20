/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/StieltjesMatrix.lean -/

import Mathlib.Data.Nat.Cast.Defs

namespace MetaMathlibExt

/-- Tridiagonal Stieltjes production matrix `S_L` with first-row parameters `a1`
and bulk parameters `a`, `b`: row 0 is `a1, 1, 0, …`, row 1 is `b1, a, 1, 0, …`,
and each row `i ≥ 2` carries `b` below the diagonal, `a` on the diagonal, `1`
above the diagonal, and `0` elsewhere. Source statements `jis_0a625f6bc81227722525070e`,
`jis_13957a12cbce86efa095f7c0`, `jis_146fe3415fbde38090082db3`, `jis_a599499d0d7c9943d0ea6c2e`;
concept `jis_sem_ccb5c04c7ffe1e3f68d34c98`. -/
def stieltjesMatrix {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) (i j : ℕ) : R :=
  if j = i + 1 then 1
  else if i = 0 ∧ j = 0 then a1
  else if i = 1 ∧ j = 0 then b1
  else if j = i then a
  else if j + 1 = i then b
  else 0

/-- Specialized Stieltjes matrix for the inverse Riordan pair with numerator
`1 - lam x - mu x ^ 2` over `1 + a x + b x ^ 2`, i.e. `a1 = a + lam` and
`b1 = b + mu`. Source statements `jis_0a625f6bc81227722525070e`,
`jis_13957a12cbce86efa095f7c0`, `jis_146fe3415fbde38090082db3`, `jis_a599499d0d7c9943d0ea6c2e`;
concept `jis_sem_ccb5c04c7ffe1e3f68d34c98`. -/
def stieltjesMatrixOf {R : Type*} [AddMonoidWithOne R] (a b lam mu : R) (i j : ℕ) : R :=
  stieltjesMatrix (a + lam) (b + mu) a b i j

end MetaMathlibExt
