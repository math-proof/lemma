/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiThetaProduct.lean -/

import Def.Analysis.SpecialFunctions.QPochhammer
import Lemma.Complex.QPochhammer
/-!
# Jacobi theta product

This file defines the product-side Jacobi theta function

`j(x; q) = (x; q)∞ (q / x; q)∞ (q; q)∞`

in terms of `MetaMathlibExt.QPochhammer.qPochhammerInf`.

The definition threads the convergence evidence `‖q‖ < 1` required by
`qPochhammerInf`. In particular, division by zero uses the
totalized field operation on `ℂ`. Analytic applications should additionally
impose `x ≠ 0`; no convergence or triple-product identity is asserted here.

## References

* [M. Dospolova, E. Kochetkova, and E. T. Mortenson, *A new Andrews--Crandall-type
  identity and the number of integer solutions to x² + 2y² + 2z² = n*][dospolova2023]
* [E. T. Mortenson, *Short proofs of Ramanujan-like identities for the eighth order mock
  theta function V₀(q)*][mortenson2023]
* [N. Borozenets and E. T. Mortenson, *On string functions of the generalized parafermionic
  theories, mock theta functions, and false theta functions*][borozenets2024]

[dospolova2023]: https://arxiv.org/abs/2307.05244
[mortenson2023]: https://arxiv.org/abs/2308.16144
[borozenets2024]: https://arxiv.org/abs/2409.14834
-/


namespace MetaMathlibExt.QPochhammer

/-- The product-side Jacobi theta function
`j(x; q) = (x; q)∞ (q / x; q)∞ (q; q)∞`, for `‖q‖ < 1`. -/
noncomputable def jacobiThetaProduct (x q : ℂ) (hq : ‖q‖ < 1) : ℂ :=
  qPochhammerInf x q hq * qPochhammerInf (q / x) q hq * qPochhammerInf q q hq

end MetaMathlibExt.QPochhammer
