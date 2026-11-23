import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Structure.JacJ1Iface
import Structure.AlgebraicGeometry_RepresentsRelSubPic

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}


def SubPicCondition.top (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ _ => True
  unit_mem := fun _ => trivial
  congr := fun _ _ _ _ _ => trivial
  pullback_mem := fun _ _ _ _ _ => trivial


namespace RepresentsRelSubPic

variable {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

noncomputable def classify (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) : SchemeHomOver t D.toBase :=
  (h.univ t M hM).choose

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard
