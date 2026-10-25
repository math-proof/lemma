import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RelSubPicGroup
import Instance.SheafOfModules_Monoidal
import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
import Lemma.Scheme.Dual_ObjPullbackL
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {V : Scheme.{u}}

end Scheme.Modules

namespace RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
  {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}

abbrev rigCorrection (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (L : (Limits.pullback c t).Modules) : T.Modules :=
  Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

namespace RigidifiedLineBundle

end RigidifiedLineBundle

end RelPicard

end AlgebraicGeometry

end
