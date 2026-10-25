import Mathlib.AlgebraicGeometry.Pullbacks
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

section Product

variable {R : Type u} [CommRing R] {B C : Scheme.{u}}
  (g : B ⟶ Spec (CommRingCat.of R)) (h : C ⟶ Spec (CommRingCat.of R))

abbrev prodStr : pullback g h ⟶ Spec (CommRingCat.of R) := pullback.fst g h ≫ g

section Points

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

end Points

namespace RelativeGroupLaw

section Unfolding

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

end Unfolding

end RelativeGroupLaw

section MapsOnPoints

variable (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h)
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

end MapsOnPoints

section Identities

variable (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h)

end Identities

end Product

end GoodReductionJacobian

end
