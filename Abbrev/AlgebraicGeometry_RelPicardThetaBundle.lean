import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Instance.SheafOfModules_Monoidal
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Abbrev.AlgebraicGeometry_ModulesDet

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))


abbrev fibreModule {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (F : (pullback c t).Modules) : (pullback (pullback.snd c t) s).Modules :=
  (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj F

end AlgebraicGeometry.RelPicard

end
