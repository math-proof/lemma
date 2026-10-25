-- Carved from Lemma/Definitions/Def_ModularCurve_TateSlots.lean: instance decls only.
import Instance.ModularCurve_TateFormal
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Lemma.ModularCurve.TateSlots

set_option autoImplicit false

noncomputable section

namespace ModularCurve

instance instIsElliptic_tateBase (K : Type*) [CommRing K] (p : ℕ) [NeZero p] :
    (tateBase K p).IsElliptic := by
  unfold tateBase; infer_instance

end ModularCurve

end
