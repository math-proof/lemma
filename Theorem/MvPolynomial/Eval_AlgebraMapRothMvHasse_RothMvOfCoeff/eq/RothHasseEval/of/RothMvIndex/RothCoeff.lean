module
public import Mathlib
public import Theorem.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


public section

/--
[rothMvHasse_eval_ofCoeff_index](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {m : ℕ} [CommRing S]
  {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMvIndex m) (x : Fin m → S) :
-- imply
  MvPolynomial.eval₂ (algebraMap ℤ S) x (rothMvHasse i (rothMvOfCoeff c)) =
    rothHasseEval c (fun h ↦ i h) x := by
-- proof
  apply rothMvHasse_eval_ofCoeff_index_h


-- created on 2026-10-21
