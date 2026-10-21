import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (P : MvPolynomial (Fin m) R) (i : RothMvIndex m) :
-- imply
  MvPolynomial.eval (0 : Fin m → R) (rothMvHasse i P) = P.coeff i := by
-- proof
  rw [MvPolynomial.eval_zero]
  change (rothMvHasse i P).coeff 0 = P.coeff i
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex]
  simp


-- created on 2026-10-21
