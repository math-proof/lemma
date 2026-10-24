import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[riordan_array_inverse_via_a_and_z_sequences_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanArrayInverse.lean)
-/
@[path]
lemma riordan_array_inverse_via_a_and_z_sequences_general
  :
-- imply
  {K : Type*} [Field K]
    (g f A Z fInv : PowerSeries K)
    (d₀₀ : K)
    (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
    (hd₀₀_ne : d₀₀ ≠ 0)
    (hf₀ : PowerSeries.constantCoeff f = 0)
    (hA₀ : PowerSeries.constantCoeff A ≠ 0)
    (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
    (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
    (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
    (hZ : g = PowerSeries.C (R := by
-- proof
  have hfSubst : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf₀
  have hfInvSubst : PowerSeries.HasSubst fInv :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hfInv₀
  have hX_eq : (PowerSeries.X : PowerSeries K) = fInv * A := by
    have e1 : PowerSeries.subst fInv f = PowerSeries.X := hcomp_left
    rw [hA, PowerSeries.subst_mul hfInvSubst, PowerSeries.subst_X hfInvSubst,
      PowerSeries.subst_comp_subst_apply hfSubst hfInvSubst, hcomp_left,
      PowerSeries.X_subst] at e1
    exact e1.symm
  have hfInv_eq : fInv = PowerSeries.X * A⁻¹ := by
    have hAinv : A * A⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hA₀
    calc fInv = fInv * 1 := (mul_one _).symm
      _ = fInv * (A * A⁻¹) := by rw [hAinv]
      _ = (fInv * A) * A⁻¹ := by ring
      _ = PowerSeries.X * A⁻¹ := by rw [← hX_eq]
  have hW_ne : PowerSeries.constantCoeff
    (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K) ≠ 0 := by
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
      PowerSeries.constantCoeff_X
    simp [hX0]
  have hCdA_ne : PowerSeries.constantCoeff
    (PowerSeries.C (R := K) d₀₀ * A : PowerSeries K) ≠ 0 := by
    have h1 : PowerSeries.constantCoeff
      (PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)
      = d₀₀ * PowerSeries.constantCoeff A := by
      simp [PowerSeries.constantCoeff_C]
    rw [h1]
    exact mul_ne_zero hd₀₀_ne hA₀
  have hS_ne : PowerSeries.constantCoeff (PowerSeries.subst fInv g) ≠ 0 := by
    have h : MvPowerSeries.constantCoeff fInv = 0 := hfInv₀
    have hS := PowerSeries.constantCoeff_subst_of_constantCoeff_zero h g
    have hS2 : MvPowerSeries.constantCoeff (PowerSeries.subst fInv g) = d₀₀ := by
      simpa [hd₀₀] using hS
    have hS3 : PowerSeries.constantCoeff (PowerSeries.subst fInv g) = d₀₀ := hS2
    rwa [hS3]
  have hW_inv : (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)⁻¹
    * (1 - PowerSeries.X * PowerSeries.subst f Z) = 1 :=
    PowerSeries.inv_mul_cancel _ hW_ne
  have hgW : g * (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
    = PowerSeries.C (R := K) d₀₀ := by
    rw [hZ, mul_assoc, hW_inv, mul_one]
  have hsubstW : PowerSeries.subst fInv
    (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
    = 1 - fInv * Z := by
    have h1 : PowerSeries.subst fInv (1 : PowerSeries K) = 1 := by
      have hC1 : (PowerSeries.C (R := K) 1) = 1 := map_one _
      rw [← hC1, PowerSeries.subst_C]
      exact map_one _
    rw [PowerSeries.subst_sub hfInvSubst, h1, PowerSeries.subst_mul hfInvSubst,
      PowerSeries.subst_X hfInvSubst,
      PowerSeries.subst_comp_subst_apply hfSubst hfInvSubst, hcomp_left,
      PowerSeries.X_subst]
  have hSU0 : PowerSeries.subst fInv g *
    PowerSeries.subst fInv
      (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
    = PowerSeries.C (R := K) d₀₀ := by
    have hsubst_gW : PowerSeries.subst fInv
      (g * (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K))
      = PowerSeries.subst fInv (PowerSeries.C (R := K) d₀₀) := by
      rw [hgW]
    rwa [PowerSeries.subst_mul hfInvSubst, PowerSeries.subst_C] at hsubst_gW
  have hSU : PowerSeries.subst fInv g * (1 - fInv * Z)
    = PowerSeries.C (R := K) d₀₀ := by
    rwa [← hsubstW]
  have hU_eq : (1 - PowerSeries.X * A⁻¹ * Z : PowerSeries K)
    = (A - PowerSeries.X * Z) * A⁻¹ := by
    rw [sub_mul, PowerSeries.mul_inv_cancel _ hA₀]
    ring
  have hSU2 : PowerSeries.subst fInv g * ((A - PowerSeries.X * Z) * A⁻¹)
    = PowerSeries.C (R := K) d₀₀ := by
    rwa [← hU_eq, ← hfInv_eq]
  have hSA : PowerSeries.subst fInv g * (A - PowerSeries.X * Z)
    = PowerSeries.C (R := K) d₀₀ * A := by
    have h := congrArg (· * A) hSU2
    rwa [mul_assoc (PowerSeries.subst fInv g) ((A - PowerSeries.X * Z) * A⁻¹) A,
      mul_assoc (A - PowerSeries.X * Z) A⁻¹ A,
      PowerSeries.inv_mul_cancel _ hA₀, mul_one] at h
  have hfirst : (PowerSeries.subst fInv g)⁻¹
    = (A - PowerSeries.X * Z) *
      ((PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)⁻¹) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hS_ne]
    have hCdA : (PowerSeries.C (R := K) d₀₀ * A)
      * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ hCdA_ne
    calc (A - PowerSeries.X * Z) * ((PowerSeries.C (R := K) d₀₀ * A)⁻¹)
      * PowerSeries.subst fInv g
      = ((A - PowerSeries.X * Z) * PowerSeries.subst fInv g)
        * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by ring
      _ = (PowerSeries.subst fInv g * (A - PowerSeries.X * Z))
        * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by
        rw [mul_comm (A - PowerSeries.X * Z) (PowerSeries.subst fInv g)]
      _ = (PowerSeries.C (R := K) d₀₀ * A)
        * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by rw [hSA]
      _ = 1 := hCdA
  exact Prod.ext hfirst hfInv_eq
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[riordan_array_inverse_via_a_and_z_sequences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanArrayInverse.lean)
-/
@[path]
lemma riordan_array_inverse_via_a_and_z_sequences
  :
-- imply
  {K : Type*} [Field K]
    (g f A Z fInv : PowerSeries K)
    (d₀₀ : K)
    (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
    (hd₀₀_ne : d₀₀ ≠ 0)
    (hf₀ : PowerSeries.constantCoeff f = 0)
    (hA₀ : PowerSeries.constantCoeff A ≠ 0)
    (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
    (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
    (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
    (hcomp_right : PowerSeries.subst f fInv = (PowerSeries.X : PowerSeries K))
    (hZ : g = PowerSeries.C (R := by
-- proof
  exact riordan_array_inverse_via_a_and_z_sequences_general g f A Z fInv d₀₀ hd₀₀ hd₀₀_ne hf₀ hA₀
    hfInv₀ hA hcomp_left hZ

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
