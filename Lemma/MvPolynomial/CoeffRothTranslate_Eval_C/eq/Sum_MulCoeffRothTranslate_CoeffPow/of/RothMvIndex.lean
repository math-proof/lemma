import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothTranslate_eval_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing S]
  (x : Fin m → S) (p : Polynomial (MvPolynomial (Fin m) S)) (y : S)
  (i : RothMvIndex m) :
-- imply
  (rothTranslate m x (Polynomial.eval (MvPolynomial.C y) p)).coeff i =
    ∑ k ∈ p.support, (rothTranslate m x (p.coeff k)).coeff i * y ^ k := by
-- proof
  apply rothTranslate_eval_coeff_h


-- created on 2026-10-21
