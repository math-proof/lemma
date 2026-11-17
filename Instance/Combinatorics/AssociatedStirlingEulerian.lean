/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingEulerian.lean -/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Card
public import Def.Combinatorics.AssociatedStirlingEulerian

@[expose] public section

namespace MetaMathlibExt

instance (r n : ℕ) : DecidablePred (IsRMinusAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRMinusAssociatedCyclePerm; infer_instance

instance (r n : ℕ) : DecidablePred (IsRAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRAssociatedCyclePerm; infer_instance

end MetaMathlibExt
