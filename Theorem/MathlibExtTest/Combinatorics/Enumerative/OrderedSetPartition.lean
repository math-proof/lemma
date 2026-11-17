/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/OrderedSetPartition.lean -/
module

public import Def.Combinatorics.Enumerative.OrderedSetPartition
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExt

example : IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]; decide

example : ¬ IsOrderedSetPartition ({0, 1} : Finset ℕ)
    [({0} : Finset ℕ), ({0, 1} : Finset ℕ)] := by
  norm_num [IsOrderedSetPartition]

end MetaMathlibExt
