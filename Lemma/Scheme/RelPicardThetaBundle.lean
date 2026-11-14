import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Instance.SheafOfModules_Monoidal
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Abbrev.AlgebraicGeometry_ModulesDet
import Def.AlgebraicGeometry_RelPicardThetaBundle
import Abbrev.AlgebraicGeometry_RelPicardThetaBundle

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))


@[simp] theorem picardBundle_def (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) :
    picardBundle c ε t M N = (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N) := rfl

@[simp] theorem thetaBundle_def (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    thetaBundle c ε t M r n = Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r))) := rfl

end AlgebraicGeometry.RelPicard

end
