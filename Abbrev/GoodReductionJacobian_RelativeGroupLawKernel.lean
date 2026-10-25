import Structure.AlgebraicGeometry_RelativeGroupLaw
import Mathlib.AlgebraicGeometry.Pullbacks

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

end RelativeGroupLaw

end GoodReductionJacobian
