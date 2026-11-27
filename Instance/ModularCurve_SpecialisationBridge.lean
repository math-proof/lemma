module
public import Theorem.HahnSeries.SpecialisationVocab
public import Instance.ModularCurve_TatePoint
public import Theorem.HahnSeries.Monodromy
public import Def.WeierstrassCurve_VariableChangePointEquiv
public import Theorem.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
public import Theorem.Thm_ModularCurve_B3_goodModel_zero_spec
public import Theorem.Thm_ModularCurve_B3_goodModel_1728_spec
public import Theorem.Thm_ModularCurve_B3_goodModel_generic_spec
public import Theorem.Thm_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728
public import Theorem.Thm_ModularCurve_B3_exists_variableChange_specialFibre_goodModel
public import Theorem.Thm_ModularCurve_B3_isElliptic_specialFibre_goodModel
public import Theorem.Thm_ModularCurve_B3_isElliptic_specialFibre
public import Theorem.Thm_ModularCurve_B3_exists_torsionBy_reduction_addEquiv
public import Def.ModularCurve_SpecialisationVocab
set_option autoImplicit false
open scoped Classical


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_SpecialisationBridge.lean: instance decls only.

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.B3

open ModularCurve.TatePoint

universe u

instance instIsElliptic_goodModel (j₀ : Qbar) : (goodModel j₀).IsElliptic := by
  unfold goodModel; infer_instance


end ModularCurve.B3

end
