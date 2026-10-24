import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousH1

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

variable {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {D : Type} [Group D] (π : H →* D)
  {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A)
  {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)

def IsLocalBridge₁ (Λ : (R ⟶ X) →+ H1 M) : Prop :=
  ∀ (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (_ : ∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x))
    (n : H → M)
    (_ : ∀ (h : H) (x : P), κ (g.hom x) (n h) = LinearMap.toAddMonoidHom ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h) x)
    (hn : n ∈ cocycles₁ M),
    Λ φ = (H1π M).hom ⟨n, hn⟩

def IsLocalBridge₂ (Λ : H1 ((ihom R).obj X) →+ continuousH2 r M) : Prop :=
  ∀ (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (_ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (_ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ (d : D) (x : P), A.ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x)
    (m : H × H → M)
    (_ : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) =
      LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (g₁, g₂)) x)
    (hm : m ∈ levelCocycles₂ r M),
    Λ ((H1π ((ihom R).obj X)).hom a) = continuousH2π r M ⟨m, hm⟩

end groupCohomology

end
