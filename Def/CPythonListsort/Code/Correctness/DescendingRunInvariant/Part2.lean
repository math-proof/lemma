/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
import Structure.CPythonListsort.Code.Correctness.DescendingRunInvariant
/-!
# Stable-order invariant for `count_run`'s descending phase

This file contains only pure list/order algebra.  The executable count-run
proof instantiates it with the range read from the transcribed machine.
-/


namespace CPythonListsort

universe u

namespace DescendingRunSpec

/-! ## Inhabited regression -/

def descendingInvariantRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def descendingInvariantThree : Occurrence Nat :=
  { value := 3, origin := 0 }

def descendingInvariantTwoOne : Occurrence Nat :=
  { value := 2, origin := 1 }

def descendingInvariantTwoTwo : Occurrence Nat :=
  { value := 2, origin := 2 }

end DescendingRunSpec
end CPythonListsort
