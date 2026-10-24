import Mathlib
import sympy.Basic
open scoped InnerProductSpace TensorProduct
open TensorProduct


namespace MathlibExt.QuantumInformation.Finite.NoCloning

/--
[no_cloning_two_state](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/NoCloning.lean)
-/
@[path]
lemma no_cloning_two_state
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ψ φ b : H}
-- given
  (_hψ : ‖ψ‖ = 1)
  (_hφ : ‖φ‖ = 1)
  (hb : ‖b‖ = 1)
  (hpos : 0 < ‖⟪ψ, φ⟫_ℂ‖)
  (hlt : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
-- imply
  ¬ ∃ (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
    U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ ∧ U (φ ⊗ₜ[ℂ] b) = φ ⊗ₜ[ℂ] φ := by
-- proof
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
  obtain hz | hz := mul_eq_zero.mp hzz
  · rw [hz, norm_zero] at hpos
    exact lt_irrefl _ hpos
  · have h1 : ⟪ψ, φ⟫_ℂ = 1 := sub_eq_zero.mp hz
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt

end MathlibExt.QuantumInformation.Finite.NoCloning


-- created on 2026-10-20
-- updated on 2026-10-23
