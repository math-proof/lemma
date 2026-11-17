module

public import Mathlib
public import Theorem.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvHasse.eq.SMul.of.RothMvIndex
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
