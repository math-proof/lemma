import Def.GaloisRep_StrictOrdinary

set_option autoImplicit false

def GaloisCharIsAdicContinuous (A : Type) [CommRing A] [IsLocalRing A]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ((χ σ : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ n

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]


@[reducible] noncomputable def twist (ρ : GaloisRepAdic A)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ) : GaloisRepAdic A where
  V := ρ.V
  finrank_eq := ρ.finrank_eq
  ρ := { toFun := fun σ => ((χ σ : Aˣ) : A) • ρ.ρ σ
         map_one' := by rw [map_one, map_one, Units.val_one, one_smul]
         map_mul' := fun σ τ => by
           rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm] }
  isAdicContinuous := by
    intro n
    obtain ⟨L₁, hL₁, h₁⟩ := ρ.isAdicContinuous n
    obtain ⟨L₂, hL₂, h₂⟩ := hχ n
    haveI := hL₁
    haveI := hL₂
    refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ v => ?_⟩
    have hσ₁ : ∀ x ∈ L₁, σ x = x := fun x hx => hσ x ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx)
    have hσ₂ : ∀ x ∈ L₂, σ x = x := fun x hx => hσ x ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx)
    have hsplit : ((χ σ : Aˣ) : A) • ρ.ρ σ v - v =
        ((χ σ : Aˣ) : A) • (ρ.ρ σ v - v) + (((χ σ : Aˣ) : A) - 1) • v := by
      rw [smul_sub, sub_smul, one_smul, sub_add_sub_cancel]
    show ((χ σ : Aˣ) : A) • ρ.ρ σ v - v ∈ _
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h₁ σ hσ₁ v))
      (Submodule.smul_mem_smul (h₂ σ hσ₂) Submodule.mem_top)

variable (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
  (hχ : GaloisCharIsAdicContinuous A χ)


noncomputable def residualTwistEquiv
    (h1 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      IsLocalRing.residue A ((χ σ : Aˣ) : A) = 1) :
    ResidualGaloisRep.Equiv (ρ.twist χ hχ).residual ρ.residual where
  toLinearEquiv := LinearEquiv.refl _ _
  map_apply σ x := by
    show ((((χ σ : Aˣ) : A) • ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)) x =
      ((ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)) x
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply,
      ← algebraMap_smul (IsLocalRing.ResidueField A) ((χ σ : Aˣ) : A),
      IsLocalRing.ResidueField.algebraMap_eq, h1 σ, one_smul]

end GaloisRepAdic
