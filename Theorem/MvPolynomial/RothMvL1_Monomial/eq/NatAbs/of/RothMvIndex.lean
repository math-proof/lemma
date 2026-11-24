module
public import Mathlib
public import Theorem.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


public section

/--
[rothMvL1_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {m : ℕ}
  (i : RothMvIndex m) (c : ℤ) :
-- imply
  rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
-- proof
  apply rothMvL1_monomial_h


-- created on 2026-10-21
