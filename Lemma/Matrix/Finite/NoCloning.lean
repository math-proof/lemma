import Mathlib
import sympy.Basic
import sympy.atlas.QuantumInformation.Finite.NoCloning
open scoped InnerProductSpace TensorProduct
open TensorProduct
open MathlibExt.QuantumInformation.Finite.NoCloning


/--
[no_cloning_two_state](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/NoCloning.lean)
-/
@[path]
private lemma no_cloning_two_state_eq
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
  apply MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_two_state ψ φ b _hψ _hφ hb hpos hlt


-- created on 2026-10-20
