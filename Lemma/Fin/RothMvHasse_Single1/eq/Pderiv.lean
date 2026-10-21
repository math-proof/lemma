import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (h : Fin m) (P : MvPolynomial (Fin m) ℚ) :
-- imply
  rothMvHasse (Finsupp.single h 1) P = MvPolynomial.pderiv h P := by
-- proof
  ext i
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    MvPolynomial.coeff_pderiv]
  have hprod :
    (∏ b : Fin m,
        (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b)
          ((Finsupp.single h 1 : RothMvIndex m) b) : ℚ)) =
      (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    ·
      simp
    ·
      intro b _ hbh
      simp [hbh]
    ·
      simp
  rw [hprod]
  ring


-- created on 2026-10-21
