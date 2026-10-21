import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothMvHasse_finSucc_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring S]
  (P : MvPolynomial (Fin (n + 1)) S) (a b : ℕ) (i : RothMvIndex n) :
-- imply
  ((MvPolynomial.finSuccEquiv S n) (rothMvHasse (i.cons a) P)).coeff b =
    rothMvHasse i
      ((Polynomial.hasseDeriv a ((MvPolynomial.finSuccEquiv S n) P)).coeff b) := by
-- proof
  apply rothMvHasse_finSucc_coeff_h


-- created on 2026-10-21
