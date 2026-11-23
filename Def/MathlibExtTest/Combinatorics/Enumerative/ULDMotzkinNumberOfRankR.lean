/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

module

public import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
public import Theorem.Finset.Enumerative.ULDMotzkinNumberOfRankR

@[expose] public section

namespace MetaMathlibExt.ULDMotzkin

def ones : Fin 1 → ℕ := fun _ => 1

end MetaMathlibExt.ULDMotzkin
