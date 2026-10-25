-- Carved from Lemma/Definitions/Def_CohCarrier_Lower.lean: instance decls only.
import Instance.CohCarrier_Level
import Def.CohCarrier_Lower

set_option autoImplicit false

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups


section LowerLeg

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ)

instance GammaHLower_finiteIndex [NeZero M] [NeZero q] : (GammaHLower M H q).FiniteIndex := by
  haveI : NeZero (q * M) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
  exact Subgroup.instFiniteIndex_subgroupOf _ _

variable (A : Type*) [AddCommGroup A]

end LowerLeg

end CohCarrier
