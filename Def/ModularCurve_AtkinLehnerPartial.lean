import Lemma.ModularCurve.X0

set_option autoImplicit false

namespace ModularCurve

section Partial

variable (N ℓ : ℕ) [NeZero ℓ]

def IsAtkinLehnerAutFull
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) : Prop :=
  ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
    σ ⟨qExpand ℚ d jq, jqd_mem_full (N * ℓ) (Dvd.dvd.mul_right hd ℓ)⟩
        = ⟨qExpand ℚ (d * ℓ) jq, jqd_mem_full (N * ℓ) (Nat.mul_dvd_mul_right hd ℓ)⟩
      ∧ σ ⟨qExpand ℚ (d * ℓ) jq, jqd_mem_full (N * ℓ) (Nat.mul_dvd_mul_right hd ℓ)⟩
        = ⟨qExpand ℚ d jq, jqd_mem_full (N * ℓ) (Dvd.dvd.mul_right hd ℓ)⟩

open Classical in

noncomputable def atkinLehnerInvolutionFull :
    modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ) :=
  if h : ∃ σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ),
      IsAtkinLehnerAutFull N ℓ σ
  then h.choose else AlgEquiv.refl

end Partial

end ModularCurve
