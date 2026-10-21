import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m) (c : R) (P : MvPolynomial (Fin m) R) :
-- imply
  rothMvHasse i (c • P) = c • rothMvHasse i P := by
-- proof
  ext k
  simp only [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    MvPolynomial.coeff_smul, smul_eq_mul]
  ring


-- created on 2026-10-21
