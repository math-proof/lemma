import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothMvL1_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (i : RothMvIndex m) (c : ℤ) :
-- imply
  rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
-- proof
  apply rothMvL1_monomial_h


-- created on 2026-10-21
