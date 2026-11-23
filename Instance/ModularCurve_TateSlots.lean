-- Carved from Lemma/Definitions/Def_ModularCurve_TateSlots.lean: instance decls only.
module

public import Instance.ModularCurve_TateFormal
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Def.ModularCurve_TateSlots
@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

instance instIsElliptic_tateBase (K : Type*) [CommRing K] (p : ℕ) [NeZero p] :
    (tateBase K p).IsElliptic := by
  unfold tateBase; infer_instance

end ModularCurve

end
