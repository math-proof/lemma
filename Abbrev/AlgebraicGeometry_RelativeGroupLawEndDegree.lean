import Mathlib
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Abbrev.GoodReductionJacobian_RelativeGroupLawKernel
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace NeronModelInfra

variable {B X : Scheme.{u}} {f : X ⟶ B}

end NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev endKer (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : Scheme.{u} :=
  pullback β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerStr (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKer β ⟶ Spec (CommRingCat.of R) :=
  pullback.snd β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerι (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : G.endKer β ⟶ A :=
  pullback.fst β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end General

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

end Field

end RelativeGroupLaw
end GoodReductionJacobian

end
