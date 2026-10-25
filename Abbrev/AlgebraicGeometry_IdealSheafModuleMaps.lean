import Abbrev.AlgebraicGeometry_IdealSheafModule

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData)

open Opposite

abbrev comapSubschemeHom : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

end AlgebraicGeometry.Scheme.IdealSheafData

end
