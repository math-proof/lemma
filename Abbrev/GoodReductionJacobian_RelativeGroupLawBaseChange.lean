import Mathlib.AlgebraicGeometry.Pullbacks
import Abbrev.GoodReductionJacobian_RelativeGroupLawKernel
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension
import Def.AlgebraicGeometry_NeronSpecialFibreRestriction
import Abbrev.GoodReductionJacobian_RelativeGroupLawFibre

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseChangeScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  pullback f ι

abbrev baseChangeStr (f : A ⟶ Spec (CommRingCat.of R)) :
    baseChangeScheme ι f ⟶ Spec (CommRingCat.of R') :=
  pullback.snd f ι


theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)


theorem baseChange_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).mul t' x y =
      baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y)) :=
  rfl

theorem baseChange_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).inv t' x = baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x)) :=
  rfl


end BaseChange

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev genericFibreScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  baseChangeScheme (specGenericFibreInclusion R K) f

abbrev genericFibreStr (f : A ⟶ Spec (CommRingCat.of R)) : genericFibreScheme K f ⟶ Spec (CommRingCat.of K) :=
  baseChangeStr (specGenericFibreInclusion R K) f


end GenericFibre

end RelativeGroupLaw
end GoodReductionJacobian

end
