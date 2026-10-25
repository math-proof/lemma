import Def.AlgebraicGeometry_FramedPolarisedAbelianScheme
import Lemma.AlgebraicGeometry.PolarisationRosati
import Structure.AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Abbrev.AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace Scheme.Modules

def tpow {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tpow M n ⊗ M

end Scheme.Modules

namespace Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def MemKernel (𝓛 : A.Modules) {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : Prop :=
  LocIsoOnBase (pullback.snd f t)
    ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules))

end Polarisation

namespace PolarisedAbelianScheme

def IsOfType (δ : Fin g → ℕ) {S : Type u} [CommRing S] (u : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S') (_ : Module.FaithfullyFlat S S') (_ : Algebra.Etale S S')
    (x : typeGroup δ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) u.f),
    (x 0 = u.L.one _ ∧ ∀ h h' : typeGroup δ, x (h + h') = u.L.mul _ (x h) (x h')) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k) (h h' : typeGroup δ),
      Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h') ∧
    (∀ (R : Type u) [CommRing R] [Algebra S' R]
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) u.f),
      Polarisation.MemKernel u.f u.L u.pol _ y ↔
        ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : typeGroup δ,
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
            Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫ (x h).1)

def HasPrincipalRoot {S : Type u} [CommRing S] (u : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
    Module.FaithfullyFlat S S' ∧
    ∀ (L' : RelativeGroupLaw S' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
          (P Q : SchemeHomOver t' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
          (L'.mul t' P Q).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
            (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
              ⟨P.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ (𝓛₀ : (pullback u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules) (a b : ℕ),
        1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
        Polarisation.KernelTrivial (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
        Polarisation.LocIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj u.pol)
          (Scheme.Modules.tpow 𝓛₀ a ⊗
            Scheme.Modules.tpow ((Scheme.Modules.pullback
              (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀) b)


namespace Satisfying

variable {Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop}

def Iso {S : Type u} [CommRing S] (X X' : Satisfying g d n Q S) : Prop :=
  PolarisedAbelianScheme.Iso X.val X'.val


end Satisfying

abbrev RootedSymmetricOfType (δ : Fin g → ℕ) : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop :=
  fun _ _ u => Polarisation.IsSymmetric u.f u.L u.pol ∧ IsOfType δ u ∧ HasPrincipalRoot u

end PolarisedAbelianScheme

end AlgebraicGeometry

end
