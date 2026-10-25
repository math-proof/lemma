-- Carved from Lemma/Definitions/Def_ModularCurve_TatePoint.lean: instance decls only.
import Instance.ModularCurve_TateFormal
import Instance.ModularCurve_PhiGen
import Lemma.WeierstrassCurve.VeluQuotientMap
import Def.ModularCurve_TatePoint

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.TatePoint

open scoped Classical in
instance instIsElliptic_nearCurve (j₀ : Qbar) : (nearCurve j₀).IsElliptic := by
  unfold nearCurve; infer_instance


end ModularCurve.TatePoint

end
