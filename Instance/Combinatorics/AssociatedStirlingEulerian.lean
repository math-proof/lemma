/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingEulerian.lean -/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Def.Combinatorics.AssociatedStirlingEulerian


namespace MetaMathlibExt

instance (r n : ℕ) : DecidablePred (IsRMinusAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRMinusAssociatedCyclePerm; infer_instance

instance (r n : ℕ) : DecidablePred (IsRAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRAssociatedCyclePerm; infer_instance

end MetaMathlibExt
