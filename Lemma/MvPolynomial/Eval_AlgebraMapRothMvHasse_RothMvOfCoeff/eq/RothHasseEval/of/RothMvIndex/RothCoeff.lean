import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothMvHasse_eval_ofCoeff_index](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing S]
  {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMvIndex m) (x : Fin m → S) :
-- imply
  MvPolynomial.eval₂ (algebraMap ℤ S) x (rothMvHasse i (rothMvOfCoeff c)) =
    rothHasseEval c (fun h ↦ i h) x := by
-- proof
  apply rothMvHasse_eval_ofCoeff_index_h


-- created on 2026-10-21
