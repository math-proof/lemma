/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
/-!
# Jordan totient function

This module defines Jordan's totient function `J_k(n)` from Yuan He,
*On the mean values of products of Dirichlet L-functions at positive
integers*, arXiv:2310.18048v3, equation (1.7) and equation (2.7).

For positive `k` and `n`, `J_k(n) = n^k * ∏_{p ∣ n} (1 - 1 / p^k)`.
We define the integral prime-factorization form and prove the exact
rational Euler product and the integer Möbius divisor sum
`∑_{d ∣ n} μ(n / d) * d^k`. The underlying `ArithmeticFunction` is
extended by `J_k(0) = 0`; the product, Möbius-sum, and rational-product
identities below hold for all `k` whenever `n ≠ 0`, generalizing the
positive-`k` source domain.
-/
namespace ArithmeticFunction
/-- Jordan totient `J_k`, integral factorization form (He (1.7)). -/
def jordanTotient (k : ℕ) : ArithmeticFunction ℕ where
  toFun n :=
    if n = 0 then 0
    else ∏ p ∈ n.primeFactors, p ^ (k * (n.factorization p - 1)) *
      (p ^ k - 1)
  map_zero' := ite_eq_left rfl
end ArithmeticFunction
