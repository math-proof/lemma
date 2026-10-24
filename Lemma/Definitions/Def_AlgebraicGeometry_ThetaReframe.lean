import Lemma.Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def IsReframe {S : Type u} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (X' : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ (P' : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P'.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P'.σ),
    X' = ⟨X.toPolarisedAbelianScheme, P', h₁, h₂⟩ ∧
    ∀ i : Fin (N + 1), P'.σ i =
      ∑ j : Fin (N + 1), ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) • X.frame.σ j

end AlgebraicGeometry.FramedPolarisedAbelianScheme

end
