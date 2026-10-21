import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m) (P Q : MvPolynomial (Fin m) R) :
-- imply
  rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
-- proof
  ext k
  simp only [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]


-- created on 2026-10-21
