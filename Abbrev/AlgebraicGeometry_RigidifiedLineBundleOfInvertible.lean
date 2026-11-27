module
public import Mathlib
public import Instance.AlgebraicGeometry_RelativePicardFunctor
public import Structure.AlgebraicGeometry_RelSubPicGroup
public import Instance.SheafOfModules_Monoidal
public import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
public import Theorem.Scheme.Dual_ObjPullbackL
public import Theorem.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
public import Theorem.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
public import Theorem.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
public import Theorem.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
set_option autoImplicit false


public section

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
