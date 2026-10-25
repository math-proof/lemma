/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyEndpoints.lean -/

import Theorem.CPythonListsort.Code.Assembly.ListSortMergePolicy
/-!
# Exact empty and singleton policy endpoints

The real top-level evaluator bypasses the scan for inputs of length zero or
one.  Consequently both executions have an empty raw policy-event stream.  At
the paper-facing normalization boundary, that same stream denotes an empty
merge plan at length zero and a literal one-leaf plan at length one.

This module pins those two endpoint cases for arbitrary comparators, reverse
flags, and validated keyed or unkeyed inputs.  In particular, the singleton
leaf is semantic normalization: it is not a fabricated `.formed` event.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The source interval represented by a validated top-level input. -/
def ListSortInput.runSpan (input : ListSortInput κ ν) : RunSpan :=
  { base := 0, len := input.slice.entries.size }

end CPythonListsort
