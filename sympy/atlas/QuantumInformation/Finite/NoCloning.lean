/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/NoCloning.lean -/

/-
  Author: @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Two-state no-cloning obstruction

This module proves the two-state pure-state no-cloning obstruction: in a complex
inner-product space, non-orthogonal non-identical unit vectors cannot both be exactly
cloned by a single complex linear isometry `H ⊗ H ≃ₗᵢ H ⊗ H` with a fixed blank state.

## Main results

* `MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_two_state` – no isometry
  clones two unit states with `0 < ‖⟪ψ, φ⟫‖ < 1` simultaneously.

## Source

W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned",
Nature 299 (1982), 802-803, DOI 10.1038/299802a0.

## Proof note

A cloning isometry preserves inner products, so with `z = ⟪ψ, φ⟫` the tensor
inner-product formula (`TensorProduct.inner_tmul`) and the unit blank state
(`⟪b, b⟫ = 1`) give `z * z = z`, hence `z = 0` or `z = 1`, contradicting
`0 < ‖z‖ < 1`. The unit hypotheses on `ψ` and `φ` are logically redundant in this
formulation but are kept in the public statement for source fidelity.
-/

open scoped InnerProductSpace TensorProduct
open TensorProduct

namespace MathlibExt.QuantumInformation.Finite.NoCloning

/-- Two-state pure-state no-cloning obstruction: in a complex inner-product space,
non-orthogonal non-identical unit vectors cannot both be exactly cloned by a single
complex linear isometry `H ⊗ H ≃ₗᵢ H ⊗ H` with a fixed blank state.
Source: W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned",
Nature 299 (1982), 802-803, DOI 10.1038/299802a0. -/
theorem no_cloning_two_state
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ b : H) (_hψ : ‖ψ‖ = 1) (_hφ : ‖φ‖ = 1) (hb : ‖b‖ = 1)
    (hpos : 0 < ‖⟪ψ, φ⟫_ℂ‖) (hlt : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
    ¬ ∃ (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
      U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ ∧ U (φ ⊗ₜ[ℂ] b) = φ ⊗ₜ[ℂ] φ := by
  rintro ⟨U, hUψ, hUφ⟩
  have hinner : ⟪ψ ⊗ₜ[ℂ] ψ, φ ⊗ₜ[ℂ] φ⟫_ℂ
      = ⟪ψ ⊗ₜ[ℂ] b, φ ⊗ₜ[ℂ] b⟫_ℂ := by
    rw [← hUψ, ← hUφ, LinearIsometryEquiv.inner_map_map]
  rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul] at hinner
  have hbb : ⟪b, b⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hb]
    norm_num
  rw [hbb, mul_one] at hinner
  have hzz : ⟪ψ, φ⟫_ℂ * (⟪ψ, φ⟫_ℂ - 1) = 0 := by
    rw [mul_sub, mul_one, hinner, sub_self]
  rcases mul_eq_zero.mp hzz with hz | hz
  · rw [hz, norm_zero] at hpos
    exact lt_irrefl _ hpos
  · have h1 : ⟪ψ, φ⟫_ℂ = 1 := sub_eq_zero.mp hz
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt

end MathlibExt.QuantumInformation.Finite.NoCloning
