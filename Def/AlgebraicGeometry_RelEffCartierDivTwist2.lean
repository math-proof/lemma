import Lemma.Scheme.Dual_ObjPullbackL
import Def.AlgebraicGeometry_RelPicardThetaBundle
import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}}


def RelEffCartierDiv.twistModule (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) : (pullback c t).Modules :=
  Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
    (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε t) ^ r).module)

end AlgebraicGeometry

end
