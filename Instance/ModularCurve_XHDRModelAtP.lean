-- Carved from Lemma/Definitions/Def_ModularCurve_XHDRModelAtP.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_XHDifferentialsModL
import Lemma.ModularCurve.XHOperators
import Abbrev.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel
import Lemma.AlgebraicCurve.CurveModel
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Abbrev.ModularCurve_XHDRModelAtP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped MatrixGroups

namespace ModularCurve

namespace XHDRLevel


instance fact_jAt_ne_zero (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Fact (jAt Γ hj ≠ 0) :=
  ⟨fun h => jqModC_rat_ne_zero (by simpa using congrArg Subtype.val h)⟩

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

variable {p Γ hj}


end XHDRLevel

open XHDRLevel


end ModularCurve

end
