-- Carved from Lemma/Definitions/Def_ModularCurve_TatePoint.lean: instance decls only.
module

public import Instance.ModularCurve_TateFormal
public import Instance.ModularCurve_PhiGen
public import Theorem.WeierstrassCurve.VeluQuotientMap
public import Def.ModularCurve_TatePoint
@[expose] public section

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.TatePoint

open scoped Classical in
instance instIsElliptic_nearCurve (j₀ : Qbar) : (nearCurve j₀).IsElliptic := by
  unfold nearCurve; infer_instance


end ModularCurve.TatePoint

end
