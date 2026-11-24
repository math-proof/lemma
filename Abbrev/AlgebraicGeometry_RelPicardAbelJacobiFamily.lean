module
public import Mathlib
public import Instance.AlgebraicGeometry_RelativePicardFunctor
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Abbrev.AlgebraicGeometry_IdealSheafModule
public import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
public import Def.AlgebraicCurve_RelCartier
public import Instance.SheafOfModules_Monoidal
public import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
public import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
set_option autoImplicit false


public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

section
variable [IsSeparated a]

abbrev pointSubBasepointModule (t ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
  (RelEffCartierDiv.ofPoint a t.1 t.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint a ε.1 ε.2).idealModule

abbrev diagDiv : RelEffCartierDiv a 1 a := RelEffCartierDiv.ofPoint a (𝟙 A) (Category.id_comp a)

end

end AlgebraicGeometry.RelPicard

end
