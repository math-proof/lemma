-- Carved from Lemma/Definitions/Def_WeierstrassCurve_Generic.lean: instance decls only.
import Mathlib
import Theorem.WeierstrassCurve.Generic
import Def.WeierstrassCurve_Generic

set_option autoImplicit false

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic


section Field

variable (K : Type u) [Field K]

instance isElliptic_curve : (curve K).IsElliptic := ⟨isUnit_Δ_curve K⟩

end Field

end WeierstrassCurve.Generic

end
