module

public import Mathlib
public import Def.NumberTheory.GeneralizedFibonacciPolynomial

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedFibonacciPolynomial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
public theorem generalizedFibonacciPolynomial_zero
  {p0 p1 d g : Polynomial ℤ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g 0 = p0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[generalizedFibonacciPolynomial_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
public theorem generalizedFibonacciPolynomial_one
  {p0 p1 d g : Polynomial ℤ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g 1 = p1 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[generalizedFibonacciPolynomial_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
public theorem generalizedFibonacciPolynomial_add_two
  {p0 p1 d g : Polynomial ℤ}
  {n : ℕ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g (n + 2) =
      d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
        g * generalizedFibonacciPolynomial p0 p1 d g n :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
