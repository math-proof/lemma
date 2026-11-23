module

public import Theorem.HahnSeries.QAdicPlace
public import Theorem.LaurentSeries.ArithmeticGalois

public noncomputable section

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Fricke

variable (N : ℕ) [NeZero N]


public theorem isFrickeAut_frickeInvolution
    (h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    IsFrickeAut N (frickeInvolution N) := by
  rw [frickeInvolution, dif_pos h]
  exact h.choose_spec


public theorem frickeInvolution_eq_refl
    (h : ¬ ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    frickeInvolution N = AlgEquiv.refl := by
  rw [frickeInvolution, dif_neg h]


public theorem cuspZero_def : cuspZero N = frickeInvolution N • cuspInfty N := rfl

end Fricke

section Full


public theorem isFrickeAutFull_frickeInvolutionFull (N : ℕ) [NeZero N]
    (h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    IsFrickeAutFull N (frickeInvolutionFull N) := by
  rw [frickeInvolutionFull, dif_pos h]
  exact h.choose_spec


public theorem frickeInvolutionFull_eq_refl (N : ℕ) [NeZero N]
    (h : ¬ ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    frickeInvolutionFull N = AlgEquiv.refl := by
  rw [frickeInvolutionFull, dif_neg h]

variable (N : ℕ) [NeZero N]


public theorem cuspZeroFull_def : cuspZeroFull N = frickeInvolutionFull N • cuspInftyFull N := rfl

end Full

section Bar


public theorem order_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : (coeffEmb L jq).order = -1 := by
  have h1 : (coeffEmb L jq).coeff (-1) ≠ 0 := by
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have h0 : coeffEmb L jq ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0
    (by rw [coeffEmb_coeff, coeff_jq_of_lt h, map_zero])

variable (N : ℕ) [NeZero N]


public theorem cuspInftyBar_toValuationSubring :
    (cuspInftyBar N).toValuationSubring
      = qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := rfl

end Bar

end ModularCurve

end
