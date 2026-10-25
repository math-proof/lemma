/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/OddLichtenbergNumbers.lean -/


import Def.NumberTheory.OddLichtenbergNumbers


namespace MetaMathlibExt

example : List.map oddLichtenberg [0, 1, 2, 3] = [1, 5, 21, 85] := by rfl

end MetaMathlibExt
