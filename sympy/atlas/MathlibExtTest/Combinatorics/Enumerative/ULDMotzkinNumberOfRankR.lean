/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/


import sympy.atlas.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR

namespace MetaMathlibExt.ULDMotzkin

private def ones : Fin 1 → ℕ := fun _ => 1

example : uldMotzkinNumber 1 ones 1 ones (by decide) 0 = 1 := by decide
example : uldMotzkinNumber 1 ones 1 ones (by decide) 2 = 2 := by decide

end MetaMathlibExt.ULDMotzkin
