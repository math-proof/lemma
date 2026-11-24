module
public import Mathlib
public import Theorem.WeierstrassCurve.ConductorLevel
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ConductorLevel.lean: instance decls only.

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

instance (W : WeierstrassCurve ℤ) : NeZero W.conductorLevel := ⟨W.conductorLevel_pos.ne'⟩

end WeierstrassCurve

end
