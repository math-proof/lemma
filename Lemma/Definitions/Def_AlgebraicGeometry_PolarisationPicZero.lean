import Lemma.Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {k : Type u} [CommRing k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

def InPicZero (M : A.Modules) : Prop :=
  Scheme.Modules.IsInvertible M ∧
    ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty ((Scheme.Modules.pullback (L.translate x)).obj M ≅ M)

def kernelPts (𝓛 : A.Modules) : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
  {x | L.IsInStabilizer 𝓛 (𝟙 (Spec (CommRingCat.of k))) x}

end AlgebraicGeometry.Polarisation

end
