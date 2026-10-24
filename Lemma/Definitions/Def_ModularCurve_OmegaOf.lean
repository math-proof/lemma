import Lemma.Definitions.Def_ModularCurve_QAdicPlace
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois
import Lemma.Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeffMap_injective
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

namespace ModularCurve

variable (N : ℕ) [NeZero N]

open scoped Classical in

def omegaOf (f : ℍ → ℂ) (σ : AlgebraicClosure ℚ →+* ℂ) :
    Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  if h : ∃ x : modularFunctionFieldBar N,
      coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
          thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
        ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)
  then
    h.choose •
      KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N)
  else 0

private theorem theta_coeffEmb_jq_coeff_neg_one :
    (thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)).coeff (-1 : ℤ) = -1 := by
  rw [thetaL_apply, theta_coeff, coeffEmb_coeff, coeff_jq_neg_one, map_one]
  norm_num

private theorem thetaL_coeffEmb_jq_ne_zero :
    thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq) ≠ 0 := by
  intro h0
  have h := theta_coeffEmb_jq_coeff_neg_one
  rw [h0] at h
  simp at h

omit [NeZero N] in

theorem omegaOf_witness_unique (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ) {x y : modularFunctionFieldBar N}
    (hx : coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ))
    (hy : coeffMap σ ((y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) : x = y := by
  have h1 : (x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)
      = (y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq) :=
    coeffMap_injective σ.injective (hx.trans hy.symm)
  have h2 : (x : LaurentSeries (AlgebraicClosure ℚ)) = y :=
    mul_right_cancel₀ thetaL_coeffEmb_jq_ne_zero h1
  exact_mod_cast h2

theorem omegaOf_eq_smul_D_of_coeffMap_eq (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ) {x : modularFunctionFieldBar N}
    (hx : coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) :
    omegaOf N f σ =
      x • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) := by
  have h : ∃ z : modularFunctionFieldBar N,
      coeffMap σ ((z : LaurentSeries (AlgebraicClosure ℚ)) *
          thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
        ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ) := ⟨x, hx⟩
  unfold omegaOf
  rw [dif_pos h, omegaOf_witness_unique N f σ h.choose_spec hx]

theorem omegaOf_eq_zero_of_not_exists (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ)
    (h : ¬ ∃ x : modularFunctionFieldBar N,
        coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
            thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
          ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) :
    omegaOf N f σ = 0 := by
  unfold omegaOf
  rw [dif_neg h]

end ModularCurve

end
