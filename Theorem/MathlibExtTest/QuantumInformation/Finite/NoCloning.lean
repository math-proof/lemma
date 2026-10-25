/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/QuantumInformation/Finite/NoCloning.lean -/


import Lemma.Matrix.Finite.NoCloning
open scoped InnerProductSpace TensorProduct

/-!
# No-cloning public-API and boundary checks

Exact-statement exercise for `NoCloning.no_cloning_two_state`, plus the identical-state
boundary case: a unit vector paired with itself has `‖⟪ψ, ψ⟫‖ = 1`, so the strict
`0 < ‖·‖ < 1` obstruction hypothesis can never fire.
-/


namespace NoCloningTest

/-- Exact public-API statement check. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ b : H) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hb : ‖b‖ = 1)
    (hpos : 0 < ‖⟪ψ, φ⟫_ℂ‖) (hlt : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
    ¬ ∃ (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
      U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ ∧ U (φ ⊗ₜ[ℂ] b) = φ ⊗ₜ[ℂ] φ :=
  MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_two_state
    ψ φ b hψ hφ hb hpos hlt

/-- Boundary: identical unit states escape the obstruction since `‖⟪ψ, ψ⟫‖ = 1`. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (hψ : ‖ψ‖ = 1) : ¬ (0 < ‖⟪ψ, ψ⟫_ℂ‖ ∧ ‖⟪ψ, ψ⟫_ℂ‖ < 1) := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  rw [hself, norm_one]
  norm_num

end NoCloningTest
