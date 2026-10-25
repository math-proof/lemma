import Lemma.ModularCurve.QAdicPlace
import Lemma.ModularCurve.ArithmeticGalois

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Fricke

variable (N : ℕ) [NeZero N]

def IsFrickeAut (σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N) : Prop :=
  σ ⟨jq, jq_mem N⟩ = ⟨jqN N, jqN_mem N⟩ ∧ σ ⟨jqN N, jqN_mem N⟩ = ⟨jq, jq_mem N⟩

open Classical in

def frickeInvolution : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N :=
  if h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ
  then h.choose else AlgEquiv.refl

theorem isFrickeAut_frickeInvolution
    (h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    IsFrickeAut N (frickeInvolution N) := by
  rw [frickeInvolution, dif_pos h]
  exact h.choose_spec

theorem frickeInvolution_eq_refl
    (h : ¬ ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    frickeInvolution N = AlgEquiv.refl := by
  rw [frickeInvolution, dif_neg h]

def cuspZero : Place ℚ (modularFunctionField N) := frickeInvolution N • cuspInfty N

theorem cuspZero_def : cuspZero N = frickeInvolution N • cuspInfty N := rfl

end Fricke

section Full

def IsFrickeAutFull (N : ℕ) [NeZero N]
    (σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N) : Prop :=
  ∀ (a b : ℕ) (hab : a * b = N) (_ : NeZero a) (_ : NeZero b),
    σ ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩
      = ⟨qExpand ℚ b jq, jqd_mem_full N (Dvd.intro_left a hab)⟩

open Classical in

def frickeInvolutionFull (N : ℕ) [NeZero N] :
    modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N :=
  if h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ
  then h.choose else AlgEquiv.refl

theorem isFrickeAutFull_frickeInvolutionFull (N : ℕ) [NeZero N]
    (h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    IsFrickeAutFull N (frickeInvolutionFull N) := by
  rw [frickeInvolutionFull, dif_pos h]
  exact h.choose_spec

theorem frickeInvolutionFull_eq_refl (N : ℕ) [NeZero N]
    (h : ¬ ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    frickeInvolutionFull N = AlgEquiv.refl := by
  rw [frickeInvolutionFull, dif_neg h]

variable (N : ℕ) [NeZero N]

def cuspZeroFull : Place ℚ (modularFunctionFieldFull N) :=
  frickeInvolutionFull N • cuspInftyFull N

theorem cuspZeroFull_def : cuspZeroFull N = frickeInvolutionFull N • cuspInftyFull N := rfl

end Full

section Bar

theorem order_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : (coeffEmb L jq).order = -1 := by
  have h1 : (coeffEmb L jq).coeff (-1) ≠ 0 := by
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have h0 : coeffEmb L jq ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0
    (by rw [coeffEmb_coeff, coeff_jq_of_lt h, map_zero])

variable (N : ℕ) [NeZero N]

def cuspInftyBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  qInftyPlaceBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩,
      order_coeffEmb_jq (AlgebraicClosure ℚ)⟩

theorem cuspInftyBar_toValuationSubring :
    (cuspInftyBar N).toValuationSubring
      = qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := rfl

end Bar

end ModularCurve

end
