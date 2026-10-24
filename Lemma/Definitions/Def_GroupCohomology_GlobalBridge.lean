import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramified

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

variable (S : Finset Nat.Primes)
  {D : Type} [Group D] (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D)
  {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep ℤ D} {A : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (ι : X →+ A)
  {p : ℕ} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (κ : B →+ M →+ A)

def IsGlobalBridge₂ (Λ : H1 ((ihom R).obj X) →+ continuousH2S S M) : Prop :=
  ∀ (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (_ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (_ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup →
        ∀ (d : D) (x : P), A.ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (_ : ∀ (g₁ g₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : P), κ (g.hom x) (m (g₁, g₂)) =
      LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (g₁, g₂)) x)
    (hm : m ∈ levelCocyclesS₂ S M),
    Λ ((H1π ((ihom R).obj X)).hom a) = continuousH2Sπ S M ⟨m, hm⟩

end groupCohomology

end
