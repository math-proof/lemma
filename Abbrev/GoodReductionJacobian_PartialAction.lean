import Mathlib
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension
import Structure.GoodReductionJacobian_PartialAction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian


namespace PartialAction

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

abbrev pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
    (x : SchemeHomOver t p) : T ⟶ pullback f p :=
  pullback.lift γ.1 x.1 (γ.2.trans x.2.symm)

end PartialAction

end GoodReductionJacobian

end
