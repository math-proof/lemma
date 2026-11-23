/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PellLucasNumber.lean -/
module

public import Def.Combinatorics.Enumerative.PellLucasNumber
public import Theorem.Finset.Enumerative.PellLucasNumber

public section

namespace MetaMathlibExt

example : pellLucas 0 = 2 := rfl

example : pellLucas 1 = 2 := rfl

example : pellLucas 2 = 6 := rfl

example : pellLucas 3 = 14 := rfl

example : pellLucas 4 = 34 := rfl

end MetaMathlibExt
