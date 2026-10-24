/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyEndpoints.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortMergePolicy

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

/-- Exact policy-accounting facts shared by the empty and singleton
top-level endpoints.  `expectedPlan` and `expectedLengths` are parameters so
the two public theorems below expose their exact normal forms in their theorem
types rather than hiding them behind an existential. -/
structure ListSortPolicyEndpointPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (result : ListSortImplResult κ ν) (expectedPlan : MergePlan)
    (expectedLengths : List Nat) : Prop where
  resultEq : (listSortTraced? lt reverse input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  policyEvents :
    (listSortTraced? lt reverse input).trace.policyEvents = []
  normalizedReplay :
    replayTopLevelMergePlan? input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents =
      some expectedPlan
  rawFormedLengths :
    PolicyEvent.formedLengths
        (listSortTraced? lt reverse input).trace.policyEvents = []
  normalizedFormedLengths :
    topLevelFormedLengths input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents =
      expectedLengths
  planRunLengths : expectedPlan.runLengths = expectedLengths
  rawLogicalMergeCost :
    PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents = 0
  planMergeCost : expectedPlan.mergeCost = 0
