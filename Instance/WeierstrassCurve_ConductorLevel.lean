-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ConductorLevel.lean: instance decls only.
import Mathlib
import Lemma.WeierstrassCurve.ConductorLevel

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

instance (W : WeierstrassCurve ℤ) : NeZero W.conductorLevel := ⟨W.conductorLevel_pos.ne'⟩

end WeierstrassCurve

end
