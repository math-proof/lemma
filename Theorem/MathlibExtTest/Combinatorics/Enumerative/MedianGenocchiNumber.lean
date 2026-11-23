/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiNumber.lean -/
module

public import Def.Combinatorics.Enumerative.MedianGenocchiNumber
public import Theorem.Finset.Enumerative.MedianGenocchiNumber

public section

namespace MetaMathlibExt

example : medianGenocchiOdd 0 = 1 := by simp

example : medianGenocchiOdd 1 = -1 := by simp

end MetaMathlibExt
