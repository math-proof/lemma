import Lemma.GaloisRep.StrictOrdinary
import Def.GaloisRep_Twist

set_option autoImplicit false


namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem galoisCharIsAdicContinuous_of_finiteLevel
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (h : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → χ σ = 1) :
    GaloisCharIsAdicContinuous A χ := by
  intro n
  obtain ⟨L, hL, hχ⟩ := h
  refine ⟨L, hL, fun σ hσ => ?_⟩
  rw [hχ σ hσ, Units.val_one, sub_self]
  exact Submodule.zero_mem _


variable (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
  (hχ : GaloisCharIsAdicContinuous A χ)

theorem twist_V : (ρ.twist χ hχ).V = ρ.V := rfl

theorem twist_ρ_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).ρ σ = ((χ σ : Aˣ) : A) • ρ.ρ σ := rfl

theorem twist_ρ_apply_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    (ρ.twist χ hχ).ρ σ v = ((χ σ : Aˣ) : A) • ρ.ρ σ v := rfl

theorem trace_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).trace σ = ((χ σ : Aˣ) : A) * ρ.trace σ := by
  show LinearMap.trace A ρ.V (((χ σ : Aˣ) : A) • ρ.ρ σ) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem det_twist_ρ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.twist χ hχ).ρ σ) = ((χ σ : Aˣ) : A) ^ 2 * LinearMap.det (ρ.ρ σ) := by
  show LinearMap.det (((χ σ : Aˣ) : A) • ρ.ρ σ) = _
  rw [LinearMap.det_smul, ρ.finrank_eq]


theorem residual_twist_isEquiv
    (h1 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      IsLocalRing.residue A ((χ σ : Aˣ) : A) = 1) :
    (ρ.twist χ hχ).residual.IsEquiv ρ.residual :=
  ⟨residualTwistEquiv ρ χ hχ h1⟩

theorem isUnramifiedAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnramifiedAt q) : (ρ.twist χ hχ).IsUnramifiedAt q := by
  intro P hP σ hσ
  rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  exact h P hP σ hσ

theorem isUnipotentOnInertiaAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnipotentOnInertiaAt q) : (ρ.twist χ hχ).IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  have e : (ρ.twist χ hχ).ρ σ = ρ.ρ σ := by
    rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  rw [e]
  exact h P hP σ hσ

theorem isStrictOrdinaryAt_twist {p : ℕ}
    (hp : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsStrictOrdinaryAt p) : (ρ.twist χ hχ).IsStrictOrdinaryAt p := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨L, hb, hD, hI, hsc⟩ := h.2 P hP
  refine ⟨L, hb, ?_, ?_, ?_⟩
  · intro σ hσ v hv
    rw [twist_ρ_apply_apply]
    exact L.smul_mem _ (hD σ hσ v hv)
  · intro σ hσ v
    rw [twist_ρ_apply_apply, hp P hP σ hσ, Units.val_one, one_smul]
    exact hI σ hσ v
  · intro σ hσ
    obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
    refine ⟨((χ σ : Aˣ) : A) * x, ((χ σ : Aˣ) : A) * z, ?_, ?_, ?_⟩
    · intro w hw
      rw [twist_ρ_apply_apply, hx w hw, smul_smul]
    · intro v
      have e : (ρ.twist χ hχ).ρ σ v - (((χ σ : Aˣ) : A) * z) • v =
          ((χ σ : Aˣ) : A) • (ρ.ρ σ v - z • v) := by
        rw [twist_ρ_apply_apply, smul_sub, smul_smul]
      rw [e]
      exact L.smul_mem _ (hz v)
    · intro n a ha
      have e : ((χ σ : Aˣ) : A) * x - (a : A) * (((χ σ : Aˣ) : A) * z) =
          ((χ σ : Aˣ) : A) * (x - (a : A) * z) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (hxz n a ha)

end GaloisRepAdic
