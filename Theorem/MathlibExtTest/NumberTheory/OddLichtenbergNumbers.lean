/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/OddLichtenbergNumbers.lean -/
module

public import Def.NumberTheory.OddLichtenbergNumbers

public section

namespace MetaMathlibExt

example : List.map oddLichtenberg [0, 1, 2, 3] = [1, 5, 21, 85] := by rfl

end MetaMathlibExt
