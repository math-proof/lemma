import Lemma.Scheme.Dual_ObjPullbackL
import Def.AlgebraicGeometry_RelPicardThetaBundle
import Lemma.AlgebraicGeometry.RelEffCartierDivOfPoint
import Def.AlgebraicGeometry_RelEffCartierDivTwist2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem RelPicard.rigSection_eq_graphOver (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    RelPicard.rigSection c t ε =
      graphOver c (t ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id]) := rfl


theorem RelEffCartierDiv.twistModule_def (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) :
    D.twistModule c ε = Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
      (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε t) ^ r).module) := rfl

end AlgebraicGeometry

end
