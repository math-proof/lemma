/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PellLucasNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.PellLucasNumber
import Lemma.Finset.Enumerative.PellLucasNumber

namespace MetaMathlibExt

example : pellLucas 0 = 2 := rfl
example : pellLucas 1 = 2 := rfl
example : pellLucas 2 = 6 := rfl
example : pellLucas 3 = 14 := rfl
example : pellLucas 4 = 34 := rfl

end MetaMathlibExt
