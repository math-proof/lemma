/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/OrderedSetPartition.lean -/


import sympy.atlas.Combinatorics.Enumerative.OrderedSetPartition
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]; decide

example : ¬ IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({0, 1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]

end MetaMathlibExt
