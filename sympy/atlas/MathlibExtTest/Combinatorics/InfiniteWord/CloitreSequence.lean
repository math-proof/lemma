/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CloitreSequence.lean -/


import sympy.atlas.Combinatorics.InfiniteWord.CloitreSequence

namespace MetaMathlibExt

example : cloitreApprox 2 = [1, 1, 2, 1, 1, 1, 1] := by decide

example : (List.range 15).map cloitreSequence =
    [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2] := by
  decide

end MetaMathlibExt
