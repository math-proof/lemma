module

public import Mathlib
public import Theorem.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvHasseAdd.eq.AddRothSMvHasse.of.RothMvIndex
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m) (P Q : MvPolynomial (Fin m) R) :
-- imply
  rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
-- proof
  ext k
  simp only [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]


-- created on 2026-10-21
