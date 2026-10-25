import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Abbrev.GoodReductionJacobian_RelativeGroupLawKernel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseResidueField (s : (Spec (CommRingCat.of R) : Scheme.{u})) : Type u :=
  (Spec (CommRingCat.of R)).residueField s

abbrev basePointInclusion (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Spec (CommRingCat.of (baseResidueField s)) ⟶ Spec (CommRingCat.of R) :=
  (Spec (CommRingCat.of R)).fromSpecResidueField s

abbrev fibreScheme (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Scheme.{u} :=
  pullback f (basePointInclusion s)

abbrev fibreStr (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    fibreScheme f s ⟶ Spec (CommRingCat.of (baseResidueField s)) :=
  pullback.snd f (basePointInclusion s)

variable (s : (Spec (CommRingCat.of R) : Scheme.{u}))

end RelativeGroupLaw
end GoodReductionJacobian

end
