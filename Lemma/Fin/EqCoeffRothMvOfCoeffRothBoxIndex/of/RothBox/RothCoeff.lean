import Mathlib
import Lemma.Fin.InjectiveRothBoxIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvOfCoeff_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ}
-- given
  (c : RothCoeff r)
  (j : RothBox r) :
-- imply
  (rothMvOfCoeff c).coeff (rothBoxIndex j) = c j := by
-- proof
  classical
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  ·
    simp
  ·
    intro k _ hkj
    simp only [ite_eq_right_iff]
    intro hidx
    exact (hkj (InjectiveRothBoxIndex hidx)).elim
  ·
    simp


-- created on 2026-10-21
