/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCollapseCost.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortMergePolicy
import sympy.atlas.CPythonListsort.Code.Assembly.PowerSortPolicyCost

/-!
# Final-collapse policy cost for the real traced evaluator

This module connects the exact selector used by `merge_force_collapse` to the
pure `CPythonForceCollapseCost` relation.  It deliberately keeps CPython's
final-collapse schedule distinct from canonical repeated-top-pair completion.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Pending-run lengths as mathematical naturals, in stack order. -/
def pendingRunLengths (state : MergeState κ ν) : List Nat :=
  state.pending.toList.map fun run => run.len.toNat
