import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R] [CommSemiring S]
  (f : R →+* S) (i : RothMvIndex m) (P : MvPolynomial (Fin m) R) :
-- imply
  MvPolynomial.map f (rothMvHasse i P) =
    rothMvHasse i (MvPolynomial.map f P) := by
-- proof
  ext k
  rw [MvPolynomial.coeff_map, CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    MvPolynomial.coeff_map, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  simp


-- created on 2026-10-21
