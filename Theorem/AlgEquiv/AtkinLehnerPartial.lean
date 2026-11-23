module

public import Theorem.HahnSeries.X0
public import Def.ModularCurve_AtkinLehnerPartial

public section

set_option autoImplicit false

namespace ModularCurve

section Partial

variable (N ℓ : ℕ) [NeZero ℓ]


public theorem isAtkinLehnerAutFull_atkinLehnerInvolutionFull
    (h : ∃ σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ),
      IsAtkinLehnerAutFull N ℓ σ) :
    IsAtkinLehnerAutFull N ℓ (atkinLehnerInvolutionFull N ℓ) := by
  rw [atkinLehnerInvolutionFull, dite_eq_left h]
  exact h.choose_spec

public theorem atkinLehnerInvolutionFull_eq_refl
    (h : ¬ ∃ σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ),
      IsAtkinLehnerAutFull N ℓ σ) :
    atkinLehnerInvolutionFull N ℓ = AlgEquiv.refl := by
  rw [atkinLehnerInvolutionFull, dite_eq_right h]

end Partial

end ModularCurve
