/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ColumnWeight.lean -/


import sympy.atlas.Combinatorics.Enumerative.ColumnWeight

namespace MetaMathlibExt

example : columnWeight 3 (fun multiplicity => multiplicity + 1)
    ([0, 1, 0] : List (Fin 3)) = 6 := by decide

end MetaMathlibExt
