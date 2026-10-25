import Structure.AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Def.AlgebraicGeometry_ModulesPullbackLocalSection

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def translate {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : pullback f t ⟶ pullback f t :=
  pullback.lift
    (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩
        (schemeHomOverComp (pullback.snd f t) rfl x)).1
    (pullback.snd f t)
    (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩
        (schemeHomOverComp (pullback.snd f t) rfl x)).2


structure ThetaPt (𝓛 : A.Modules) {R : Type u} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) where

  pt : SchemeHomOver t f

  iso : (Scheme.Modules.pullback (translate f L t pt)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

def act (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤) :=

  (θ.iso.hom.app ((translate f L t θ.pt) ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackLocalSection (translate f L t θ.pt) s) :
    Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, (translate f L t θ.pt) ⁻¹ᵁ ⊤))

end ThetaPt

def baseScalar {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (r : R) :
    Γ(pullback f t, ⊤) :=
  (pullback.snd f t).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

structure SchrodingerFrame (𝓛 : A.Modules) {R : Type u} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] where

  σ : ((i : Fin g) → ZMod (δ i)) → Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)

  basis : Function.Bijective fun c : ((i : Fin g) → ZMod (δ i)) → R => ∑ h, baseScalar f t (c h) • σ h

  lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt f L 𝓛 t

  dualLift : AddChar ((i : Fin g) → ZMod (δ i)) R → ThetaPt f L 𝓛 t

  lift_act : ∀ h h', (lift h).act (σ h') = σ (h + h')

  dualLift_act : ∀ χ h, (dualLift χ).act (σ h) = baseScalar f t (χ h) • σ h

end AlgebraicGeometry.Polarisation

end
