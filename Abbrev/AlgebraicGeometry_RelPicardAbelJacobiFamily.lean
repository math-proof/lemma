import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
import Def.AlgebraicCurve_RelCartier
import Instance.SheafOfModules_Monoidal
import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option autoImplicit false

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
