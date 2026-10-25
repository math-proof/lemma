import Lemma.AlgebraicGeometry.ThetaGroupAction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def IsThetaAdapted (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type u} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ F : Polarisation.SchrodingerFrame X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) δ,
    ∀ i : Fin (N + 1),
      F.σ (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))

end FramedPolarisedAbelianScheme

namespace PolarisedAbelianScheme

variable {g N n : ℕ}

def ThetaTypeLocally (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] :
    ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g (N + 1) n S → Prop :=
  fun S _ u =>
    ∀ (R : Type u) [CommRing R] [Algebra S R] (ζ : R),
      ζ ^ (N + 1) = 1 → (∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) →
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
        Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
        ∃ (X' : FramedPolarisedAbelianScheme g N n R') (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i))),
          PolarisedAbelianScheme.IsPullback ((algebraMap R R').comp (algebraMap S R)) u X'.toPolarisedAbelianScheme ∧
          X'.IsThetaAdapted δ e

end PolarisedAbelianScheme

end AlgebraicGeometry

end
