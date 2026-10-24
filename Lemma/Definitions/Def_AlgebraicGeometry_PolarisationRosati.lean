import Lemma.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Lemma.Definitions.Def_SheafOfModules_MonoidalV2

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def idPt : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

def negMor : A ⟶ A := (L.inv f (idPt f)).1

theorem negMor_over : negMor f L ≫ f = f := (L.inv f (idPt f)).2

def addMor : pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem addMor_over : addMor f L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

def LocIsoOnBase {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S')) (M M' : X.Modules) : Prop :=
  ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M')

def IsSymmetric (𝓛 : A.Modules) : Prop :=
  LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) 𝓛

def mumfordBundle (𝓛 : A.Modules) : (pullback f f).Modules :=
  (Scheme.Modules.pullback (addMor f L)).obj 𝓛 ⊗
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛) ⊗
      (Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛))

def sliceAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ x.1) (by rw [Category.assoc, x.2]; exact pullback.condition)

def KernelTrivial (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) →
      x = L.one t

def KernelIsTwoTorsion (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) ↔
      L.mul t x x = L.one t

def RosatiCompatible (𝓛 : A.Modules) {I : Type v} (ι : I → (A ⟶ A)) (hι : ∀ b, ι b ≫ f = f) (star : I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase (pullback.fst f f ≫ f)
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ ι b)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f ≫ ι (star b)) (pullback.snd f f)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))

end AlgebraicGeometry.Polarisation

end
