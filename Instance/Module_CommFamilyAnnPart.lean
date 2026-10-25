-- Carved from Lemma/Definitions/Def_Module_CommFamilyAnnPart.lean: instance decls only.
import Mathlib
import Lemma.Module.CommFamilyAnnPart

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace Module.End

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (σ : Type*)

variable {K V σ}

namespace CommFamily

variable (F : CommFamily K V σ)

instance commRing_adjoin : CommRing F.adjoin where
  __ := (inferInstance : Ring F.adjoin)
  mul_comm a b := F.isMulCommutative_adjoin.is_comm.comm a b

end CommFamily

end Module.End
