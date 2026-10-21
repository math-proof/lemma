import Mathlib
import Lemma.Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
import Lemma.Fin.RothPolyL1.le.MulAdd_1RothMvL1.of.RothMvIndex
import Lemma.Polynomial.Map_AlgebraMapRothLastSlice.eq.MulCCoeff.of.EqRothLastEquiv_MapAlgebraMap_MulC_MapAlgebraMapMapC.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin
open Polynomial


/--
[roth_exists_integral_factor_data](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
-- given
  (d : RothDeterminantData P r) :
-- imply
  Nonempty (RothIntegralFactorData d) := by
-- proof
  classical
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr d.V_ne
  have hcoeff : d.V.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  let WZ := rothLastSlice d.U i
  have hmapW : Polynomial.map (algebraMap ℤ ℚ) WZ =
    Polynomial.C (d.V.coeff i : ℚ) * d.W := by
    exact Map_AlgebraMapRothLastSlice.eq.MulCCoeff.of.EqRothLastEquiv_MapAlgebraMap_MulC_MapAlgebraMapMapC.RothMvIndex
      d.U d.V d.W i d.factorization
  exact ⟨{
    coeffIndex := i
    coeff_ne := hcoeff
    WZ := WZ
    WZ_ne := by
      intro hzero
      exact (mul_ne_zero
        (Polynomial.C_ne_zero.mpr (mod_cast hcoeff : (d.V.coeff i : ℚ) ≠ 0))
        d.W_ne)
        (by rw [← hmapW, hzero, Polynomial.map_zero])
    WZ_degree := LeNatDegreeRothLastSlice.of.RothMvIndex d.U_degree i
    WZ_l1 := (RothPolyL1.le.MulAdd_1RothMvL1.of.RothMvIndex d.U_degree i).trans
      (Nat.mul_le_mul_left _ d.U_l1)
    scaled_factorization := by
      rw [map_smul, d.factorization, hmapW, Polynomial.map_mul, Polynomial.map_C]
      simp only [Algebra.smul_def]
      have hC :
        algebraMap ℚ (Polynomial (MvPolynomial (Fin n) ℚ))
          (d.V.coeff i : ℚ) =
        Polynomial.C (MvPolynomial.C (d.V.coeff i : ℚ)) := by
        simp
      rw [hC]
      ring
  }⟩


-- created on 2026-10-21
