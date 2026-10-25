/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/SmarandachePermutationSequence.lean -/


import Def.Combinatorics.Enumerative.SmarandachePermutationSequence
import Lemma.Finset.Enumerative.SmarandachePermutationSequence


namespace MetaMathlibExt

example : smarandacheBlock 4 = [1, 3, 5, 7, 8, 6, 4, 2] := by rfl

example : List.map smarandachePermutation (List.range 6) = [1, 2, 1, 3, 4, 2] := by rfl

end MetaMathlibExt
