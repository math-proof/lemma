import Lemma.Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Lemma.Definitions.Def_AlgebraicGeometry_PolarisationRosati

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

abbrev typeGroup {g : ℕ} (δ : Fin g → ℕ) : Type := ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))

variable {g d n : ℕ}

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

structure Satisfying (g d n : ℕ) (Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (S : Type u) [CommRing S] where

  val : PolarisedAbelianScheme g d n S

  prop : Q S val

namespace Satisfying

variable {Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop}

def Iso {S : Type u} [CommRing S] (X X' : Satisfying g d n Q S) : Prop :=
  PolarisedAbelianScheme.Iso X.val X'.val

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S') : Prop :=
  PolarisedAbelianScheme.IsPullback φ X.val X'.val

structure IsFineModuli (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    {B : Type} [CommRing B] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      Satisfying g d n Q S → SchemeHomOver s πM) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), Iso X X' → pt S s X = pt S s X'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S'),
    IsPullback φ X X' → (pt S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s X).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ X : Satisfying g d n Q S, pt S s X = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), pt S s X = pt S s X' → Iso X X'

end Satisfying

abbrev RootedSymmetricOfType (δ : Fin g → ℕ) : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop :=
  fun _ _ u => Polarisation.IsSymmetric u.f u.L u.pol ∧ IsOfType δ u ∧ HasPrincipalRoot u

end PolarisedAbelianScheme

end AlgebraicGeometry

end
