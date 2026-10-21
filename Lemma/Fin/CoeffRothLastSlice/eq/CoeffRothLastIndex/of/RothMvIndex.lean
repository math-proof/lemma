import Mathlib
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastSlice_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (P : MvPolynomial (Fin (n + 1)) ℤ)
  (i : RothMvIndex n)
  (a : ℕ) :
-- imply
  (rothLastSlice P i).coeff a = P.coeff (rothLastIndex i a) := by
-- proof
  classical
  rw [rothLastSlice, Polynomial.finsetSum_coeff]
  if ha : a ∈ (rothLastEquiv ℤ n P).support then
    rw [Finset.sum_eq_single a]
    ·
      simp [CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
    ·
      intro b hb hba
      simp [Polynomial.coeff_monomial, hba]
    ·
      exact fun hnot ↦ (hnot ha).elim
  else
    rw [Finset.sum_eq_zero]
    ·
      rw [← CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
      simpa using (congrArg (fun Q : MvPolynomial (Fin n) ℤ ↦ Q.coeff i)
        (Polynomial.notMem_support_iff.mp ha)).symm
    ·
      intro b hb
      have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
      simp [Polynomial.coeff_monomial, hba]


-- created on 2026-10-21
