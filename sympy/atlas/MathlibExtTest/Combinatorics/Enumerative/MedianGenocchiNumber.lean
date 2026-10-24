/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiNumber
import Lemma.Finset.Enumerative.MedianGenocchiNumber

namespace MetaMathlibExt

example : medianGenocchiOdd 0 = 1 := by simp
example : medianGenocchiOdd 1 = -1 := by simp

end MetaMathlibExt
