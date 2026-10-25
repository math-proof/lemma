import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace ModularCurve

namespace TwoChart

variable (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K]


abbrev XFin : Scheme.{u} := Spec (CommRingCat.of (chartAlgFin A K j))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartAlgInf A K j))

abbrev XMid : Scheme.{u} := Spec (CommRingCat.of (chartAlgMid A K j))

abbrev fFin : XMid A K j ⟶ XFin A K j := Spec.map (CommRingCat.ofHom (inclFin A K j).toRingHom)

abbrev fInf : XMid A K j ⟶ XInf A K j := Spec.map (CommRingCat.ofHom (inclInf A K j).toRingHom)


theorem ιFin_modelTo : ιFin A K j ≫ modelTo A K j =
    Spec.map (CommRingCat.ofHom (algebraMap A (chartAlgFin A K j))) :=
  pushout.inl_desc _ _ _


end TwoChart

end ModularCurve

end
